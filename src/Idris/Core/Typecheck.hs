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
recheck ctxt env tm orig
   = let v = next_tvar ctxt in
       case runStateT (check' False ctxt env tm) (v, []) of -- holes banned
          Error (IncompleteTerm _) -> Error $ IncompleteTerm orig
          Error e -> Error e
          OK ((tm, ty), constraints) ->
              do checkUnique ctxt env tm
                 return (tm, ty, constraints)

check :: Context -> Env -> Raw -> TC (Term, Type)
check ctxt env tm 
     = evalStateT (check' True ctxt env tm) (0, []) -- Holes allowed

check' :: Bool -> Context -> Env -> Raw -> StateT UCs TC (Term, Type)
check' holes ctxt env top = chk env top where
  chk env (Var n)
      | Just (i, ty) <- lookupTyEnv n env = return (P Bound n ty, ty)
      | (P nt n' ty : _) <- lookupP n ctxt = return (P nt n' ty, ty)
      | otherwise = do lift $ tfail $ NoSuchVariable n
  chk env (RApp f a)
      = do (fv, fty) <- chk env f
           (av, aty) <- chk env a
           let fty' = case uniqueBinders (map fst env) (finalise fty) of
                        ty@(Bind x (Pi s) t) -> ty
                        _ -> uniqueBinders (map fst env)
                                 $ case hnf ctxt env fty of
                                     ty@(Bind x (Pi s) t) -> ty
                                     _ -> normalise ctxt env fty
           case fty' of
             Bind x (Pi s) t ->
                 do convertsC ctxt env aty s
                    let apty = simplify initContext env
                                        (Bind x (Let aty av) t)
                    return (App fv av, apty)
             t -> lift $ tfail $ NonFunctionType fv fty 
  chk env RType
    | holes = return (TType (UVal 0), TType (UVal 0))
    | otherwise = do (v, cs) <- get
                     let c = ULT (UVar v) (UVar (v+1))
                     put (v+2, (c:cs))
                     return (TType (UVar v), TType (UVar (v+1)))
  chk env (RUType u)
    | holes = return (UType u, TType (UVal 0))
    | otherwise = do -- TODO! (v, cs) <- get
                     -- let c = ULT (UVar v) (UVar (v+1))
                     -- put (v+2, (c:cs))
                     -- return (TType (UVar v), TType (UVar (v+1)))
                     return (UType u, TType (UVal 0))
  chk env (RConstant Forgot) = return (Erased, Erased)
  chk env (RConstant c) = return (Constant c, constType c)
    where constType (I _)   = Constant (AType (ATInt ITNative))
          constType (BI _)  = Constant (AType (ATInt ITBig))
          constType (Fl _)  = Constant (AType ATFloat)
          constType (Ch _)  = Constant (AType (ATInt ITChar))
          constType (Str _) = Constant StrType
          constType (B8 _)  = Constant (AType (ATInt (ITFixed IT8)))
          constType (B16 _) = Constant (AType (ATInt (ITFixed IT16)))
          constType (B32 _) = Constant (AType (ATInt (ITFixed IT32)))
          constType (B64 _) = Constant (AType (ATInt (ITFixed IT64)))
          constType (B8V  a) = Constant (AType (ATInt (ITVec IT8  (V.length a))))
          constType (B16V a) = Constant (AType (ATInt (ITVec IT16 (V.length a))))
          constType (B32V a) = Constant (AType (ATInt (ITVec IT32 (V.length a))))
          constType (B64V a) = Constant (AType (ATInt (ITVec IT64 (V.length a))))
          constType Forgot  = Erased
          constType _       = TType (UVal 0)
  chk env (RForce t) = do (_, ty) <- chk env t
                          return (Erased, ty)
  chk env (RBind n (Pi s) t)
      = do (sv, st) <- chk env s
           (tv, tt) <- chk ((n, Pi sv) : env) t
           (v, cs) <- get
           case (normalise ctxt env st, normalise ctxt env tt) of
                (TType su, TType tu) -> do
                    when (not holes) $ put (v+1, ULE su (UVar v):ULE tu (UVar v):cs)
                    return (Bind n (Pi (uniqueBinders (map fst env) sv))
                              (pToV n tv), TType (UVar v))
                (UType u, _) ->
                    return (Bind n (Pi (uniqueBinders (map fst env) sv))
                                (pToV n tv), UType u)
                (_, UType u) ->
                    return (Bind n (Pi (uniqueBinders (map fst env) sv))
                                (pToV n tv), UType u)
  chk env (RBind n b sc)
      = do b' <- checkBinder b
           (scv, sct) <- chk ((n, b'):env) sc
           discharge n b' (pToV n scv) (pToV n sct)
    where checkBinder (Lam t)
            = do (tv, tt) <- chk env t
                 let tv' = normalise ctxt env tv
                 let tt' = normalise ctxt env tt
                 lift $ isType ctxt env tt'
                 return (Lam tv)
          checkBinder (Let t v)
            = do (tv, tt) <- chk env t
                 (vv, vt) <- chk env v
                 let tv' = normalise ctxt env tv
                 let tt' = normalise ctxt env tt
                 convertsC ctxt env vt tv
                 lift $ isType ctxt env tt'
                 return (Let tv vv)
          checkBinder (NLet t v)
            = do (tv, tt) <- chk env t
                 (vv, vt) <- chk env v
                 let tv' = normalise ctxt env tv
                 let tt' = normalise ctxt env tt
                 convertsC ctxt env vt tv
                 lift $ isType ctxt env tt'
                 return (NLet tv vv)
          checkBinder (Hole t)
            | not holes = lift $ tfail (IncompleteTerm undefined)
            | otherwise
                   = do (tv, tt) <- chk env t
                        let tv' = normalise ctxt env tv
                        let tt' = normalise ctxt env tt
                        lift $ isType ctxt env tt'
                        return (Hole tv)
          checkBinder (GHole i t)
            = do (tv, tt) <- chk env t
                 let tv' = normalise ctxt env tv
                 let tt' = normalise ctxt env tt
                 lift $ isType ctxt env tt'
                 return (GHole i tv)
          checkBinder (Guess t v)
            | not holes = lift $ tfail (IncompleteTerm undefined)
            | otherwise
                   = do (tv, tt) <- chk env t
                        (vv, vt) <- chk env v
                        let tv' = normalise ctxt env tv
                        let tt' = normalise ctxt env tt
                        convertsC ctxt env vt tv
                        lift $ isType ctxt env tt'
                        return (Guess tv vv)
          checkBinder (PVar t)
            = do (tv, tt) <- chk env t
                 let tv' = normalise ctxt env tv
                 let tt' = normalise ctxt env tt
                 lift $ isType ctxt env tt'
                 -- Normalised version, for erasure purposes (it's easier
                 -- to tell if it's a collapsible variable)
                 return (PVar tv)
          checkBinder (PVTy t)
            = do (tv, tt) <- chk env t
                 let tv' = normalise ctxt env tv
                 let tt' = normalise ctxt env tt
                 lift $ isType ctxt env tt'
                 return (PVTy tv)

          discharge n (Lam t) scv sct
            = return (Bind n (Lam t) scv, Bind n (Pi t) sct)
          discharge n (Pi t) scv sct
            = return (Bind n (Pi t) scv, sct)
          discharge n (Let t v) scv sct
            = return (Bind n (Let t v) scv, Bind n (Let t v) sct)
          discharge n (NLet t v) scv sct
            = return (Bind n (NLet t v) scv, Bind n (Let t v) sct)
          discharge n (Hole t) scv sct
            = return (Bind n (Hole t) scv, sct)
          discharge n (GHole i t) scv sct
            = return (Bind n (GHole i t) scv, sct)
          discharge n (Guess t v) scv sct
            = return (Bind n (Guess t v) scv, sct)
          discharge n (PVar t) scv sct
            = return (Bind n (PVar t) scv, Bind n (PVTy t) sct)
          discharge n (PVTy t) scv sct
            = return (Bind n (PVTy t) scv, sct)

-- If any binders are of kind 'UniqueType' or 'AllTypes' and the name appears
-- in the scope more than once, this is an error.
checkUnique :: Context -> Env -> Term -> TC ()
checkUnique ctxt env tm = evalStateT (chkBinders env (explicitNames tm)) []
  where 
    chkBinders :: Env -> Term -> StateT [(Name, Bool)] TC ()
    chkBinders env (V i) | length env > i = chkName (fst (env!!i))
    chkBinders env (P _ n _) = chkName n
    chkBinders env (App f a) = do chkBinders env f; chkBinders env a
    chkBinders env (Bind n b t)
       = do chkBinderName env n b
            chkBinders ((n, b) : env) t
    chkBinders env t = return ()

    chkBinderName :: Env -> Name -> Binder Term -> StateT [(Name, Bool)] TC ()
    chkBinderName env n b
       = do let rawty = forgetEnv (map fst env) (binderTy b)
            (_, kind) <- lift $ check ctxt env rawty -- FIXME: Cache in binder?
            case kind of
                 UType UniqueType -> do ns <- get
                                        put ((n, False) : ns)
                 UType AllTypes -> do ns <- get
                                      put ((n, False) : ns)
                 _ -> return ()
            chkBinders env (binderTy b)
            case b of
                 Let t v -> chkBinders env v
                 _ -> return ()

    chkName n 
       = do ns <- get
            case lookup n ns of
                 Nothing -> return ()
                 Just True -> lift $ tfail (UniqueError n)
                 Just False -> put ((n, True) : filter (\x -> fst x /= n) ns)

