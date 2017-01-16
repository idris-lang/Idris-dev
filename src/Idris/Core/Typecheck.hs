{-|
Module      : Idris.Core.Typecheck
Description : Idris' type checker.
Copyright   :
License     : BSD3
Maintainer  : The Idris Community.
-}

{-# LANGUAGE DeriveFunctor, FlexibleInstances, MultiParamTypeClasses,
             PatternGuards #-}

module Idris.Core.Typecheck where

import Idris.Core.Evaluate
import Idris.Core.TT
import Idris.Core.WHNF

import Control.Monad.State
import qualified Data.Vector.Unboxed as V (length)
import Debug.Trace

-- To check conversion, normalise each term wrt the current environment.
-- Since we haven't converted everything to de Bruijn indices yet, we'll have to
-- deal with alpha conversion - we do this by making each inner term de Bruijn
-- indexed with 'finalise'

convertsC :: Context -> Env -> Term -> Term -> StateT UCs TC ()
convertsC ctxt env x y =
    do let hs = map fstEnv (filter isHole env)
       c1 <- convEq ctxt hs x y
       if c1 then return ()
         else
            do c2 <- convEq ctxt hs (finalise (normalise ctxt env x))
                         (finalise (normalise ctxt env y))
               if c2 then return ()
                 else lift $ tfail (CantConvert
                             (finalise (normalise ctxt env x))
                             (finalise (normalise ctxt env y)) (errEnv env))

converts :: Context -> Env -> Term -> Term -> TC ()
converts ctxt env x y
     = let hs = map fstEnv (filter isHole env) in
       case convEq' ctxt hs x y of
          OK True -> return ()
          _ -> case convEq' ctxt hs (finalise (normalise ctxt env x))
                                    (finalise (normalise ctxt env y)) of
                OK True -> return ()
                _ -> tfail (CantConvert
                           (finalise (normalise ctxt env x))
                           (finalise (normalise ctxt env y)) (errEnv env))

isHole (n, _, Hole _) = True
isHole _ = False

errEnv = map (\(x, _, b) -> (x, binderTy b))

isType :: Context -> Env -> Term -> TC ()
isType ctxt env tm = isType' (normalise ctxt env tm)
    where isType' tm | isUniverse tm = return ()
                     | otherwise = fail (showEnv env tm ++ " is not a Type")

convType :: String -> Context -> Env -> Term -> StateT UCs TC ()
convType tcns ctxt env tm =
    do (v, cs) <- get
       put (v + 1, cs)
       case normalise ctxt env tm of
            UType _ -> return ()
            _ -> convertsC ctxt env tm (TType (UVar tcns v))

recheck :: String -> Context -> Env -> Raw -> Term -> TC (Term, Type, UCs)
recheck = recheck_borrowing False []

recheck_borrowing :: Bool -> [Name] -> String -> Context -> Env -> Raw -> Term ->
                     TC (Term, Type, UCs)
recheck_borrowing uniq_check bs tcns ctxt env tm orig
   = let v = next_tvar ctxt in
       case runStateT (check' False tcns ctxt env tm) (v, []) of -- holes banned
          Error (IncompleteTerm _) -> Error $ IncompleteTerm orig
          Error e -> Error e
          OK ((tm, ty), constraints) ->
              do when uniq_check $ checkUnique bs ctxt env tm
                 return (tm, ty, constraints)

check :: Context -> Env -> Raw -> TC (Term, Type)
check ctxt env tm
     -- Holes allowed, so constraint namespace doesn't matter
     = evalStateT (check' True [] ctxt env tm) (0, [])

check' :: Bool -> String -> Context -> Env -> Raw -> StateT UCs TC (Term, Type)
check' holes tcns ctxt env top
   = do (tm, ty, _) <- chk Rig1 (TType (UVar tcns (-5))) Nothing env top
        return (tm, ty)
 where

  smaller (UType NullType) _ = UType NullType
  smaller _ (UType NullType) = UType NullType
  smaller (UType u)        _ = UType u
  smaller _        (UType u) = UType u
  smaller x        _         = x

  astate | holes = MaybeHoles
         | otherwise = Complete

  chk :: RigCount -> -- multiplicity (need enough in context to produce this many of the term)
         Type -> -- uniqueness level
         Maybe UExp -> -- universe for kind
         Env -> Raw -> StateT UCs TC (Term, Type, [Name])
  chk rigc u lvl env (Var n)
      | Just (i, erig, ty) <- lookupTyEnv n env
             = case rigSafe holes erig rigc n of
                    Nothing -> return (P Bound n ty, ty, used rigc n)
                    Just msg -> lift $ tfail $ Msg msg
      -- If we're elaborating, we don't want the private names; if we're
      -- checking an already elaborated term, we do
      | [P nt n' ty] <- lookupP_all (not holes) True n ctxt
             = return (P nt n' ty, ty, [])
--       -- If the names are ambiguous, require it to be fully qualified
--       | [P nt n' ty] <- lookupP_all (not holes) True n ctxt
--              = return (P nt n' ty, ty, [])
      | otherwise = do lift $ tfail $ NoSuchVariable n
    where rigSafe True _    _    n = Nothing
          rigSafe _    Rig1 RigW n = Just ("Trying to use linear name " ++ show n ++ " in non-linear context")
          rigSafe _    Rig0 RigW n = Just ("Trying to use irrelevant name " ++ show n ++ " in relevant context")
          rigSafe _    _    _    n = Nothing

          used Rig0 n = []
          used _ n = [n]

  chk rigc u lvl env ap@(RApp f RType) | not holes
    -- special case to reduce constraintss
      = do (fv, fty, fns) <- chk rigc u Nothing env f
           let fty' = case uniqueBinders (map fstEnv env) (finalise fty) of
                        ty@(Bind x (Pi _ i s k) t) -> ty
                        _ -> uniqueBinders (map fstEnv env)
                                 $ case normalise ctxt env fty of
                                     ty@(Bind x (Pi _ i s k) t) -> ty
                                     _ -> normalise ctxt env fty
           case fty' of
             Bind x (Pi rig i (TType v') k) t ->
               do (v, cs) <- get
                  put (v+1, ULT (UVar tcns v) v' : cs)
                  let apty = simplify initContext env
                                 (Bind x (Let (TType v') (TType (UVar tcns v))) t)
                  return (App Complete fv (TType (UVar tcns v)), apty, fns)
             Bind x (Pi rig i s k) t ->
                 do (av, aty, _) <- chk rigc u Nothing env RType
                    convertsC ctxt env aty s
                    let apty = simplify initContext env
                                        (Bind x (Let aty av) t)
                    return (App astate fv av, apty, fns)
             t -> lift $ tfail $ NonFunctionType fv fty
  chk rigc u lvl env ap@(RApp f a)
      = do (fv, fty, fns) <- chk rigc u Nothing env f
           let (rigf, fty') =
                   case uniqueBinders (map fstEnv env) (finalise fty) of
                        ty@(Bind x (Pi rig i s k) t) -> (rig, ty)
                        _ -> case normalise ctxt env fty of
                                  ty@(Bind x (Pi rig i s k) t) ->
                                     (rig, uniqueBinders (map fstEnv env) ty)
                                  _ -> (RigW, uniqueBinders (map fstEnv env)
                                                    (normalise ctxt env fty)) -- This is an error, caught below...
           (av, aty, ans) <- chk (rigMult rigc rigf) u Nothing env a
           case fty' of
             Bind x (Pi rig i s k) t ->
                 do convertsC ctxt env aty s
                    let apty = simplify initContext env
                                        (Bind x (Let aty av) t)
                    return (App astate fv av, apty, fns ++ ans)
             t -> lift $ tfail $ NonFunctionType fv fty
  chk rigc u lvl env RType
    | holes = return (TType (UVal 0), TType (UVal 0), [])
    | otherwise = do (v, cs) <- get
                     let c = ULT (UVar tcns v) (UVar tcns (v+1))
                     put (v+2, (c:cs))
                     return (TType (UVar tcns v), TType (UVar tcns (v+1)), [])
  chk rigc u lvl env (RUType un)
    | holes = return (UType un, TType (UVal 0), [])
    | otherwise = do -- TODO! Issue #1715 on the issue tracker.
                     -- https://github.com/idris-lang/Idris-dev/issues/1715
                     -- (v, cs) <- get
                     -- let c = ULT (UVar v) (UVar (v+1))
                     -- put (v+2, (c:cs))
                     -- return (TType (UVar v), TType (UVar (v+1)))
                     return (UType un, TType (UVal 0), [])
  chk rigc u lvl env (RConstant Forgot) = return (Erased, Erased, [])
  chk rigc u lvl env (RConstant c) = return (Constant c, constType c, [])
    where constType (I _)   = Constant (AType (ATInt ITNative))
          constType (BI _)  = Constant (AType (ATInt ITBig))
          constType (Fl _)  = Constant (AType ATFloat)
          constType (Ch _)  = Constant (AType (ATInt ITChar))
          constType (Str _) = Constant StrType
          constType (B8 _)  = Constant (AType (ATInt (ITFixed IT8)))
          constType (B16 _) = Constant (AType (ATInt (ITFixed IT16)))
          constType (B32 _) = Constant (AType (ATInt (ITFixed IT32)))
          constType (B64 _) = Constant (AType (ATInt (ITFixed IT64)))
          constType TheWorld = Constant WorldType
          constType Forgot  = Erased
          constType _       = TType (UVal 0)
  chk rigc u lvl env (RBind n (Pi rig i s k) t)
      = do (sv, st, sns) <- chk Rig0 u Nothing (envZero env) s
           when (rig == RigW) $
                lift $ linearCheckArg ctxt (normalise ctxt env sv)
           (v, cs) <- get
           (kv, kt, _) <- chk Rig0 u Nothing (envZero env) k -- no need to validate these constraints, they are independent
           put (v+1, cs)
           let maxu = case lvl of
                           Nothing -> UVar tcns v
                           Just v' -> v'
           (tv, tt, tns) <- chk Rig0 st (Just maxu) ((n, Rig0, Pi Rig0 i sv kv) : envZero env) t

--            convertsC ctxt env st (TType maxu)
--            convertsC ctxt env tt (TType maxu)
--            when holes $ put (v, cs)
--            return (Bind n (Pi i (uniqueBinders (map fst env) sv) (TType maxu))
--                      (pToV n tv), TType maxu)

           case (normalise ctxt env st, normalise ctxt env tt) of
                (TType su, TType tu) -> do
                    when (not holes) $ do (v, cs) <- get
                                          put (v, ULE su maxu :
                                                  ULE tu maxu : cs)
                    let k' = TType (UVar tcns v) `smaller` st `smaller` kv `smaller` u
                    return (Bind n (Pi rig i (uniqueBinders (map fstEnv env) sv) k')
                              (pToV n tv), k', sns ++ tns)
                (un, un') ->
                   let k' = st `smaller` kv `smaller` un `smaller` un' `smaller` u in
                    return (Bind n (Pi rig i (uniqueBinders (map fstEnv env) sv) k')
                                (pToV n tv), k', sns ++ tns)

      where mkUniquePi kv (Bind n (Pi rig i s k) sc)
                    = let k' = smaller kv k in
                          Bind n (Pi rig i s k') (mkUniquePi k' sc)
            mkUniquePi kv (Bind n (Lam rig t) sc)
                    = Bind n (Lam rig (mkUniquePi kv t)) (mkUniquePi kv sc)
            mkUniquePi kv (Bind n (Let t v) sc)
                    = Bind n (Let (mkUniquePi kv t) v) (mkUniquePi kv sc)
            mkUniquePi kv t = t

            -- Kind of the whole thing is the kind of the most unique thing
            -- in the environment (because uniqueness taints everything...)
            mostUnique [] k = k
            mostUnique (Pi _ _ _ pk : es) k = mostUnique es (smaller pk k)
            mostUnique (_ : es) k = mostUnique es k

  chk rigc u lvl env (RBind n b sc)
      = do (b', bt', bns) <- checkBinder b
           (scv, sct, scns) <- chk rigc (smaller bt' u) Nothing ((n, getCount b, b'):env) sc
           when (getCount b == RigW) $
             lift $ linearCheckArg ctxt (normalise ctxt env (binderTy b'))
           checkUsageOK (getCount b) scns
           discharge n b' bt' (pToV n scv) (pToV n sct) (bns ++ scns)
    where getCount (Pi rig _ _ _) = rigMult rigc rig
          getCount (PVar rig _) = rigMult rigc rig
          getCount (Lam rig _) = rigMult rigc rig
          getCount _ = rigMult rigc RigW

          checkUsageOK Rig0 _ = return ()
          checkUsageOK RigW _ = return ()
          checkUsageOK Rig1 ns
              = let used = length (filter (==n) ns) in
                    if used == 1 then return ()
                       else lift $ tfail $ Msg $ "There are " ++ (show used) ++
                              " uses of linear name " ++ show n

          checkBinder (Lam rig t)
            = do (tv, tt, _) <- chk Rig0 u Nothing (envZero env) t
                 let tv' = normalise ctxt env tv
                 convType tcns ctxt env tt
                 return (Lam rig tv, tt, [])
          checkBinder (Let t v)
            = do (tv, tt, _) <- chk Rig0 u Nothing (envZero env) t
                 -- May have multiple uses, check at RigW
                 -- (or rather, like an application of a lambda, multiply)
                 -- (Consider: adding a single use let?)
                 (vv, vt, vns) <- chk (rigMult rigc RigW) u Nothing env v
                 let tv' = normalise ctxt env tv
                 convertsC ctxt env vt tv
                 convType tcns ctxt env tt
                 return (Let tv vv, tt, vns)
          checkBinder (NLet t v)
            = do (tv, tt, _) <- chk Rig0 u Nothing (envZero env) t
                 (vv, vt, vns) <- chk rigc u Nothing env v
                 let tv' = normalise ctxt env tv
                 convertsC ctxt env vt tv
                 convType tcns ctxt env tt
                 return (NLet tv vv, tt, vns)
          checkBinder (Hole t)
            | not holes = lift $ tfail (IncompleteTerm undefined)
            | otherwise
                   = do (tv, tt, _) <- chk Rig0 u Nothing (envZero env) t
                        let tv' = normalise ctxt env tv
                        convType tcns ctxt env tt
                        return (Hole tv, tt, [])
          checkBinder (GHole i ns t)
            = do (tv, tt, _) <- chk Rig0 u Nothing (envZero env) t
                 let tv' = normalise ctxt env tv
                 convType tcns ctxt env tt
                 return (GHole i ns tv, tt, [])
          checkBinder (Guess t v)
            | not holes = lift $ tfail (IncompleteTerm undefined)
            | otherwise
                   = do (tv, tt, _) <- chk Rig0 u Nothing (envZero env) t
                        (vv, vt, vns) <- chk rigc u Nothing env v
                        let tv' = normalise ctxt env tv
                        convertsC ctxt env vt tv
                        convType tcns ctxt env tt
                        return (Guess tv vv, tt, vns)
          checkBinder (PVar rig t)
            = do (tv, tt, _) <- chk Rig0 u Nothing (envZero env) t
                 let tv' = normalise ctxt env tv
                 convType tcns ctxt env tt
                 -- Normalised version, for erasure purposes (it's easier
                 -- to tell if it's a collapsible variable)
                 return (PVar rig tv, tt, [])
          checkBinder (PVTy t)
            = do (tv, tt, _) <- chk Rig0 u Nothing (envZero env) t
                 let tv' = normalise ctxt env tv
                 convType tcns ctxt env tt
                 return (PVTy tv, tt, [])

          discharge n (Lam r t) bt scv sct ns
            = return (Bind n (Lam r t) scv, Bind n (Pi r Nothing t bt) sct, ns)
          discharge n (Pi r i t k) bt scv sct ns
            = return (Bind n (Pi r i t k) scv, sct, ns)
          discharge n (Let t v) bt scv sct ns
            = return (Bind n (Let t v) scv, Bind n (Let t v) sct, ns)
          discharge n (NLet t v) bt scv sct ns
            = return (Bind n (NLet t v) scv, Bind n (Let t v) sct, ns)
          discharge n (Hole t) bt scv sct ns
            = return (Bind n (Hole t) scv, sct, ns)
          discharge n (GHole i ns t) bt scv sct uns
            = return (Bind n (GHole i ns t) scv, sct, uns)
          discharge n (Guess t v) bt scv sct ns
            = return (Bind n (Guess t v) scv, sct, ns)
          discharge n (PVar r t) bt scv sct ns
            = return (Bind n (PVar r t) scv, Bind n (PVTy t) sct, ns)
          discharge n (PVTy t) bt scv sct ns
            = return (Bind n (PVTy t) scv, sct, ns)

-- Number of times a name can be used
data UniqueUse = Never -- no more times
               | Once -- at most once more
               | LendOnly -- only under 'lend'
               | Many -- unlimited
  deriving Eq

-- If any binders are of kind 'UniqueType' or 'AllTypes' and the name appears
-- in the scope more than once, this is an error.
checkUnique :: [Name] -> Context -> Env -> Term -> TC ()
checkUnique borrowed ctxt env tm
         = evalStateT (chkBinders env (explicitNames tm)) []
  where
    isVar (P _ _ _) = True
    isVar (V _) = True
    isVar _ = False

    chkBinders :: Env -> Term -> StateT [(Name, (UniqueUse, Universe))] TC ()
    chkBinders env (V i) | length env > i = chkName (fstEnv (env!!i))
    chkBinders env (P _ n _) = chkName n
    -- 'lending' a unique or nulltype variable doesn't count as a use,
    -- but we still can't lend something that's already been used.
    chkBinders env (App _ (App _ (P _ (NS (UN lend) [owner]) _) t) a)
       | isVar a && owner == txt "Ownership" &&
         (lend == txt "lend" || lend == txt "Read")
            = do chkBinders env t -- Check the type normally
                 st <- get
                 -- Remove the 'LendOnly' names from the unusable set
                 put (filter (\(n, (ok, _)) -> ok /= LendOnly) st)
                 chkBinders env a
                 put st -- Reset the old state after checking the argument
    chkBinders env (App _ f a) = do chkBinders env f; chkBinders env a
    chkBinders env (Bind n b t)
       = do chkBinderName env n b
            st <- get
            case b of
                 Let t v -> chkBinders env v
                 _ -> return ()
            chkBinders ((n, Rig0, b) : env) t
    chkBinders env t = return ()

    chkBinderName :: Env -> Name -> Binder Term ->
                     StateT [(Name, (UniqueUse, Universe))] TC ()
    chkBinderName env n b
       = do let rawty = forgetEnv (map fstEnv env) (binderTy b)
            (_, kind) <- lift $ check ctxt env rawty
            case kind of
                 UType UniqueType -> do ns <- get
                                        if n `elem` borrowed
                                           then put ((n, (LendOnly, NullType)) : ns)
                                           else put ((n, (Once, UniqueType)) : ns)
                 UType NullType -> do ns <- get
                                      put ((n, (Many, NullType)) : ns)
                 UType AllTypes -> do ns <- get
                                      put ((n, (Once, AllTypes)) : ns)
                 _ -> return ()

    chkName n
       = do ns <- get
            case lookup n ns of
                 Nothing -> return ()
                 Just (Many, k) -> return ()
                 Just (Never, k) -> lift $ tfail (UniqueError k n)
                 Just (LendOnly, k) -> lift $ tfail (UniqueError k n)
                 Just (Once, k) -> put ((n, (Never, k)) :
                                              filter (\x -> fst x /= n) ns)
