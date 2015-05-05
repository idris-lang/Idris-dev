{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances, DeriveFunctor,
             PatternGuards #-}

module Idris.Core.Typecheck where

import Control.Monad.State
import Debug.Trace
import qualified Data.Vector.Unboxed as V (length)

import Idris.Core.TT
import Idris.Core.Evaluate

-- To check conversion, normalise each term wrt the current environment.
-- Since we haven't converted everything to de Bruijn indices yet, we'll have to
-- deal with alpha conversion - we do this by making each inner term de Bruijn
-- indexed with 'finalise'

convertsC :: Context -> Env -> Term -> Term -> StateT UCs TC ()
convertsC ctxt env x y =
    do let hs = map fst (filter isHole env)
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
     = let hs = map fst (filter isHole env) in
       case convEq' ctxt hs x y of
          OK True -> return ()
          _ -> case convEq' ctxt hs (finalise (normalise ctxt env x))
                                    (finalise (normalise ctxt env y)) of
                OK True -> return ()
                _ -> tfail (CantConvert
                           (finalise (normalise ctxt env x))
                           (finalise (normalise ctxt env y)) (errEnv env))

isHole (n, Hole _) = True
isHole _ = False

errEnv = map (\(x, b) -> (x, binderTy b))

isType :: Context -> Env -> Term -> TC ()
isType ctxt env tm = isType' (normalise ctxt env tm)
    where isType' tm | isUniverse tm = return ()
                     | otherwise = fail (showEnv env tm ++ " is not a Type")

recheck :: Context -> Env -> Raw -> Term -> TC (Term, Type, UCs)
recheck = recheck_borrowing False []

recheck_borrowing :: Bool -> [Name] -> Context -> Env -> Raw -> Term ->
                     TC (Term, Type, UCs)
recheck_borrowing uniq_check bs ctxt env tm orig
   = let v = next_tvar ctxt in
       case runStateT (check' False ctxt env tm) (v, []) of -- holes banned
          Error (IncompleteTerm _) -> Error $ IncompleteTerm orig
          Error e -> Error e
          OK ((tm, ty), constraints) ->
              do when uniq_check $ checkUnique bs ctxt env tm
                 return (tm, ty, constraints)

check :: Context -> Env -> Raw -> TC (Term, Type)
check ctxt env tm
     = evalStateT (check' True ctxt env tm) (0, []) -- Holes allowed

check' :: Bool -> Context -> Env -> Raw -> StateT UCs TC (Term, Type)
check' holes ctxt env top = chk (TType (UVar (-5))) env top where

  smaller (UType NullType) _ = UType NullType
  smaller _ (UType NullType) = UType NullType
  smaller (UType u)        _ = UType u
  smaller _        (UType u) = UType u
  smaller x        _         = x

  astate | holes = MaybeHoles
         | otherwise = Complete

  chk :: Type -> -- uniqueness level
         Env -> Raw -> StateT UCs TC (Term, Type)
  chk u env (Var n)
      | Just (i, ty) <- lookupTyEnv n env = return (P Bound n ty, ty)
      -- If we're elaborating, we don't want the private names; if we're
      -- checking an already elaborated term, we do
      | [P nt n' ty] <- lookupP_all (not holes) n ctxt 
             = return (P nt n' ty, ty)
      | otherwise = do lift $ tfail $ NoSuchVariable n
  chk u env ap@(RApp f RType) | not holes
    -- special case to reduce constraintss
      = do (fv, fty) <- chk u env f
           let fty' = case uniqueBinders (map fst env) (finalise fty) of
                        ty@(Bind x (Pi i s k) t) -> ty
                        _ -> uniqueBinders (map fst env)
                                 $ case hnf ctxt env fty of
                                     ty@(Bind x (Pi i s k) t) -> ty
                                     _ -> normalise ctxt env fty
           case fty' of
             Bind x (Pi i (TType v') k) t ->
               do (v, cs) <- get
                  put (v+1, ULT (UVar v) v' : cs)
                  let apty = simplify initContext env
                                 (Bind x (Let (TType v') (TType (UVar v))) t)
                  return (App Complete fv (TType (UVar v)), apty)
             Bind x (Pi i s k) t ->
                 do (av, aty) <- chk u env RType 
                    convertsC ctxt env aty s
                    let apty = simplify initContext env
                                        (Bind x (Let aty av) t)
                    return (App astate fv av, apty)
             t -> lift $ tfail $ NonFunctionType fv fty
  chk u env ap@(RApp f a)
      = do (fv, fty) <- chk u env f
           let fty' = case uniqueBinders (map fst env) (finalise fty) of
                        ty@(Bind x (Pi i s k) t) -> ty
                        _ -> uniqueBinders (map fst env)
                                 $ case hnf ctxt env fty of
                                     ty@(Bind x (Pi i s k) t) -> ty
                                     _ -> normalise ctxt env fty
           (av, aty) <- chk u env a
           case fty' of
             Bind x (Pi i s k) t ->
                 do convertsC ctxt env aty s
                    let apty = simplify initContext env
                                        (Bind x (Let aty av) t)
                    return (App astate fv av, apty)
             t -> lift $ tfail $ NonFunctionType fv fty
  chk u env RType
    | holes = return (TType (UVal 0), TType (UVal 0))
    | otherwise = do (v, cs) <- get
                     let c = ULT (UVar v) (UVar (v+1))
                     put (v+2, (c:cs))
                     return (TType (UVar v), TType (UVar (v+1)))
  chk u env (RUType un)
    | holes = return (UType un, TType (UVal 0))
    | otherwise = do -- TODO! Issue #1715 on the issue tracker.
                     -- https://github.com/idris-lang/Idris-dev/issues/1715
                     -- (v, cs) <- get
                     -- let c = ULT (UVar v) (UVar (v+1))
                     -- put (v+2, (c:cs))
                     -- return (TType (UVar v), TType (UVar (v+1)))
                     return (UType un, TType (UVal 0))
  chk u env (RConstant Forgot) = return (Erased, Erased)
  chk u env (RConstant c) = return (Constant c, constType c)
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
  chk u env (RForce t) 
      = do (_, ty) <- chk u env t
           return (Erased, ty)
  chk u env (RBind n (Pi i s k) t)
      = do (sv, st) <- chk u env s
           (v, cs) <- get
           (kv, kt) <- chk u env k -- no need to validate these constraints, they are independent
           put (v+1, cs)
           let maxu = UVar v
           (tv, tt) <- chk st ((n, Pi i sv kv) : env) t
           case (normalise ctxt env st, normalise ctxt env tt) of
                (TType su, TType tu) -> do
                    when (not holes) $ do (v, cs) <- get
                                          put (v, ULE su maxu : 
                                                  ULE tu maxu : cs)
                    let k' = TType (UVar v) `smaller` st `smaller` kv `smaller` u
                    return (Bind n (Pi i (uniqueBinders (map fst env) sv) k')
                              (pToV n tv), k')
                (un, un') ->
                   let k' = st `smaller` kv `smaller` un `smaller` un' `smaller` u in
                    return (Bind n (Pi i (uniqueBinders (map fst env) sv) k')
                                (pToV n tv), k')

      where mkUniquePi kv (Bind n (Pi i s k) sc)
                    = let k' = smaller kv k in
                          Bind n (Pi i s k') (mkUniquePi k' sc)
            mkUniquePi kv (Bind n (Lam t) sc)
                    = Bind n (Lam (mkUniquePi kv t)) (mkUniquePi kv sc)
            mkUniquePi kv (Bind n (Let t v) sc)
                    = Bind n (Let (mkUniquePi kv t) v) (mkUniquePi kv sc)
            mkUniquePi kv t = t

            -- Kind of the whole thing is the kind of the most unique thing
            -- in the environment (because uniqueness taints everything...)
            mostUnique [] k = k
            mostUnique (Pi _ _ pk : es) k = mostUnique es (smaller pk k)
            mostUnique (_ : es) k = mostUnique es k

  chk u env (RBind n b sc)
      = do (b', bt') <- checkBinder b
           (scv, sct) <- chk (smaller bt' u) ((n, b'):env) sc
           discharge n b' bt' (pToV n scv) (pToV n sct)
    where checkBinder (Lam t)
            = do (tv, tt) <- chk u env t
                 let tv' = normalise ctxt env tv
                 let tt' = normalise ctxt env tt
                 lift $ isType ctxt env tt'
                 return (Lam tv, tt')
          checkBinder (Let t v)
            = do (tv, tt) <- chk u env t
                 (vv, vt) <- chk u env v
                 let tv' = normalise ctxt env tv
                 let tt' = normalise ctxt env tt
                 convertsC ctxt env vt tv
                 lift $ isType ctxt env tt'
                 return (Let tv vv, tt')
          checkBinder (NLet t v)
            = do (tv, tt) <- chk u env t
                 (vv, vt) <- chk u env v
                 let tv' = normalise ctxt env tv
                 let tt' = normalise ctxt env tt
                 convertsC ctxt env vt tv
                 lift $ isType ctxt env tt'
                 return (NLet tv vv, tt')
          checkBinder (Hole t)
            | not holes = lift $ tfail (IncompleteTerm undefined)
            | otherwise
                   = do (tv, tt) <- chk u env t
                        let tv' = normalise ctxt env tv
                        let tt' = normalise ctxt env tt
                        lift $ isType ctxt env tt'
                        return (Hole tv, tt')
          checkBinder (GHole i t)
            = do (tv, tt) <- chk u env t
                 let tv' = normalise ctxt env tv
                 let tt' = normalise ctxt env tt
                 lift $ isType ctxt env tt'
                 return (GHole i tv, tt')
          checkBinder (Guess t v)
            | not holes = lift $ tfail (IncompleteTerm undefined)
            | otherwise
                   = do (tv, tt) <- chk u env t
                        (vv, vt) <- chk u env v
                        let tv' = normalise ctxt env tv
                        let tt' = normalise ctxt env tt
                        convertsC ctxt env vt tv
                        lift $ isType ctxt env tt'
                        return (Guess tv vv, tt')
          checkBinder (PVar t)
            = do (tv, tt) <- chk u env t
                 let tv' = normalise ctxt env tv
                 let tt' = normalise ctxt env tt
                 lift $ isType ctxt env tt'
                 -- Normalised version, for erasure purposes (it's easier
                 -- to tell if it's a collapsible variable)
                 return (PVar tv, tt')
          checkBinder (PVTy t)
            = do (tv, tt) <- chk u env t
                 let tv' = normalise ctxt env tv
                 let tt' = normalise ctxt env tt
                 lift $ isType ctxt env tt'
                 return (PVTy tv, tt')

          discharge n (Lam t) bt scv sct
            = return (Bind n (Lam t) scv, Bind n (Pi Nothing t bt) sct)
          discharge n (Pi i t k) bt scv sct
            = return (Bind n (Pi i t k) scv, sct)
          discharge n (Let t v) bt scv sct
            = return (Bind n (Let t v) scv, Bind n (Let t v) sct)
          discharge n (NLet t v) bt scv sct
            = return (Bind n (NLet t v) scv, Bind n (Let t v) sct)
          discharge n (Hole t) bt scv sct
            = return (Bind n (Hole t) scv, sct)
          discharge n (GHole i t) bt scv sct
            = return (Bind n (GHole i t) scv, sct)
          discharge n (Guess t v) bt scv sct
            = return (Bind n (Guess t v) scv, sct)
          discharge n (PVar t) bt scv sct
            = return (Bind n (PVar t) scv, Bind n (PVTy t) sct)
          discharge n (PVTy t) bt scv sct
            = return (Bind n (PVTy t) scv, sct)

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
    chkBinders env (V i) | length env > i = chkName (fst (env!!i))
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
            chkBinders ((n, b) : env) t
    chkBinders env t = return ()

    chkBinderName :: Env -> Name -> Binder Term ->
                     StateT [(Name, (UniqueUse, Universe))] TC ()
    chkBinderName env n b
       = do let rawty = forgetEnv (map fst env) (binderTy b)
            (_, kind) <- lift $ check ctxt env rawty -- FIXME: Cache in binder?
                                                     -- Issue #1714 on the issue tracker
                                                     -- https://github.com/idris-lang/Idris-dev/issues/1714
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
