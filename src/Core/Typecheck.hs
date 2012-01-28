{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances, DeriveFunctor,
             PatternGuards #-}

module Core.Typecheck where

import Control.Monad.State
import Debug.Trace

import Core.TT
import Core.Evaluate

-- To check conversion, normalise each term wrt the current environment.
-- Since we haven't converted everything to de Bruijn indices yet, we'll have to
-- deal with alpha conversion - we do this by making each inner term de Bruijn
-- indexed with 'finalise'

convertsC :: Context -> Env -> Term -> Term -> StateT UCs TC ()
convertsC ctxt env x y 
   = do c <- convEq ctxt (finalise (normalise ctxt env x))
                         (finalise (normalise ctxt env y))
        if c then return ()
             else fail ("Can't convert between " ++ 
                        showEnv env (finalise (normalise ctxt env x)) ++ " and " ++ 
                        showEnv env (finalise (normalise ctxt env y)))

converts :: Context -> Env -> Term -> Term -> TC ()
converts ctxt env x y = if (finalise (normalise ctxt env x) == 
                            finalise (normalise ctxt env y))
                          then return ()
                          else fail ("Can't convert between " ++ 
                                     showEnvDbg env (finalise (normalise ctxt env x)) ++ " and " ++ 
                                     showEnvDbg env (finalise (normalise ctxt env y)))

isSet :: Context -> Env -> Term -> TC ()
isSet ctxt env tm = isSet' (normalise ctxt env tm)
    where isSet' (Set _) = return ()
          isSet' tm = fail (showEnv env tm ++ " is not a Set")

recheck :: Context -> Env -> Raw -> Term -> TC (Term, Type, UCs)
recheck ctxt env tm orig
   = let v = next_tvar ctxt in
       case runStateT (check' False ctxt env tm) (v, []) of -- holes banned
          Error (IncompleteTerm _) -> Error $ IncompleteTerm orig
          Error e -> Error e
          OK ((tm, ty), constraints) -> 
              return (tm, ty, constraints)

check :: Context -> Env -> Raw -> TC (Term, Type)
check ctxt env tm = evalStateT (check' True ctxt env tm) (0, []) -- Holes allowed

check' :: Bool -> Context -> Env -> Raw -> StateT UCs TC (Term, Type)
check' holes ctxt env top = chk env top where
  chk env (Var n)
      | Just (i, ty) <- lookupTyEnv n env = return (P Bound n ty, ty)
      | (P nt n' ty : _) <- lookupP Nothing n ctxt = return (P nt n' ty, ty)
      | otherwise = do lift $ tfail $ NoSuchVariable n
  chk env (RApp f a)
      = do (fv, fty) <- chk env f
           (av, aty) <- chk env a
           let fty' = renameBinders 0 $ normalise ctxt env fty
           case fty' of
             Bind x (Pi s) t ->
                 do convertsC ctxt env aty s
                    let apty = normalise initContext env (Bind x (Let aty av) t)
                    return (App fv av, apty)
             t -> fail "Can't apply a non-function type"
    -- This rather unpleasant hack is needed because during incomplete 
    -- proofs, variables are locally bound with an explicit name. If we just 
    -- make sure bound names in function types are locally unique, machine
    -- generated names, we'll be fine.
    where renameBinders i (Bind x (Pi s) t) = Bind (MN i "binder") (Pi s) 
                                                   (renameBinders (i+1) t)
          renameBinders i sc = sc
  chk env RSet 
    | holes = return (Set (UVal 0), Set (UVal 0))
    | otherwise = do (v, cs) <- get
                     let c = ULT (UVar v) (UVar (v+1))
                     put (v+2, (c:cs))
                     return (Set (UVar v), Set (UVar (v+1)))
  chk env (RConstant Forgot) = return (Erased, Erased)
  chk env (RConstant c) = return (Constant c, constType c)
    where constType (I _)   = Constant IType
          constType (BI _)  = Constant BIType
          constType (Fl _)  = Constant FlType
          constType (Ch _)  = Constant ChType
          constType (Str _) = Constant StrType
          constType Forgot  = Erased
          constType _       = Set (UVal 0)
  chk env (RForce t) = do (_, ty) <- chk env t
                          return (Erased, ty)
  chk env (RBind n (Pi s) t)
      = do (sv, st) <- chk env s
           (tv, tt) <- chk ((n, Pi sv) : env) t
           (v, cs) <- get
           let Set su = normalise ctxt env st
           let Set tu = normalise ctxt env tt
           when (not holes) $ put (v+1, ULE su (UVar v):ULE tu (UVar v):cs)
           return (Bind n (Pi sv) (pToV n tv), Set (UVar v))  
  chk env (RBind n b sc)
      = do b' <- checkBinder b
           (scv, sct) <- chk ((n, b'):env) sc
           discharge n b' (pToV n scv) (pToV n sct)
    where checkBinder (Lam t)
            = do (tv, tt) <- chk env t
                 let tv' = normalise ctxt env tv
                 let tt' = normalise ctxt env tt
                 lift $ isSet ctxt env tt'
                 return (Lam tv)
          checkBinder (Pi t)
            = do (tv, tt) <- chk env t
                 let tv' = normalise ctxt env tv
                 let tt' = normalise ctxt env tt
                 lift $ isSet ctxt env tt'
                 return (Pi tv)
          checkBinder (Let t v)
            = do (tv, tt) <- chk env t
                 (vv, vt) <- chk env v
                 let tv' = normalise ctxt env tv
                 let tt' = normalise ctxt env tt
                 convertsC ctxt env vt tv
                 lift $ isSet ctxt env tt'
                 return (Let tv vv)
          checkBinder (NLet t v)
            = do (tv, tt) <- chk env t
                 (vv, vt) <- chk env v
                 let tv' = normalise ctxt env tv
                 let tt' = normalise ctxt env tt
                 convertsC ctxt env vt tv
                 lift $ isSet ctxt env tt'
                 return (NLet tv vv)
          checkBinder (Hole t)
            | not holes = lift $ tfail (IncompleteTerm undefined)
            | otherwise
                   = do (tv, tt) <- chk env t
                        let tv' = normalise ctxt env tv
                        let tt' = normalise ctxt env tt
                        lift $ isSet ctxt env tt'
                        return (Hole tv)
          checkBinder (GHole t)
            = do (tv, tt) <- chk env t
                 let tv' = normalise ctxt env tv
                 let tt' = normalise ctxt env tt
                 lift $ isSet ctxt env tt'
                 return (GHole tv)
          checkBinder (Guess t v)
            | not holes = lift $ tfail (IncompleteTerm undefined)
            | otherwise
                   = do (tv, tt) <- chk env t
                        (vv, vt) <- chk env v
                        let tv' = normalise ctxt env tv
                        let tt' = normalise ctxt env tt
                        convertsC ctxt env vt tv
                        lift $ isSet ctxt env tt'
                        return (Guess tv vv)
          checkBinder (PVar t)
            = do (tv, tt) <- chk env t
                 let tv' = normalise ctxt env tv
                 let tt' = normalise ctxt env tt
                 lift $ isSet ctxt env tt'
                 return (PVar tv)
          checkBinder (PVTy t)
            = do (tv, tt) <- chk env t
                 let tv' = normalise ctxt env tv
                 let tt' = normalise ctxt env tt
                 lift $ isSet ctxt env tt'
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
            = do -- A hole can't appear in the type of its scope
                 checkNotHoley 0 sct
                 return (Bind n (Hole t) scv, sct)
          discharge n (GHole t) scv sct
            = do -- A hole can't appear in the type of its scope
                 checkNotHoley 0 sct
                 return (Bind n (GHole t) scv, sct)
          discharge n (Guess t v) scv sct
            = do -- A hole can't appear in the type of its scope
                 checkNotHoley 0 sct
                 return (Bind n (Guess t v) scv, sct)
          discharge n (PVar t) scv sct
            = return (Bind n (PVar t) scv, Bind n (PVTy t) sct)
          discharge n (PVTy t) scv sct
            = return (Bind n (PVTy t) scv, sct)
  
          checkNotHoley i (V v) 
              | v == i = fail "You can't put a hole where a hole don't belong"
          checkNotHoley i (App f a) = do checkNotHoley i f
                                         checkNotHoley i a
          checkNotHoley i (Bind n b sc) = checkNotHoley (i+1) sc
          checkNotHoley _ _ = return ()


checkProgram :: Context -> RProgram -> TC Context
checkProgram ctxt [] = return ctxt
checkProgram ctxt ((n, RConst t) : xs) 
   = do (t', tt') <- trace (show n) $ check ctxt [] t
        isSet ctxt [] tt'
        checkProgram (addTyDecl n t' ctxt) xs
checkProgram ctxt ((n, RFunction (RawFun ty val)) : xs)
   = do (ty', tyt') <- trace (show n) $ check ctxt [] ty
        (val', valt') <- check ctxt [] val
        isSet ctxt [] tyt'
        converts ctxt [] ty' valt'
        checkProgram (addToCtxt n val' ty' ctxt) xs
checkProgram ctxt ((n, RData (RDatatype _ ty cons)) : xs)
   = do (ty', tyt') <- trace (show n) $ check ctxt [] ty
        isSet ctxt [] tyt'
        -- add the tycon temporarily so we can check constructors
        let ctxt' = addDatatype (Data n 0 ty' []) ctxt
        cons' <- mapM (checkCon ctxt') cons
        checkProgram (addDatatype (Data n 0 ty' cons') ctxt) xs
  where checkCon ctxt (n, cty) = do (cty', ctyt') <- check ctxt [] cty
                                    return (n, cty')


