{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances, DeriveFunctor #-}

module Core.Typecheck where

import Control.Monad.State
import Debug.Trace

import Core.Core
import Core.Evaluate

-- To check conversion, normalise each term wrt the current environment.
-- Since we haven't converted everything to de Bruijn indices yet, we'll have to
-- deal with alpha conversion - we do this by making each inner term de Bruijn
-- indexed with 'finalise'

converts :: Context -> Env -> Term -> Term -> TC ()
converts ctxt env x y = if (finalise (normalise ctxt env x) == 
                            finalise (normalise ctxt env y))
                          then return ()
                          else fail ("Can't convert between " ++ 
                                     showEnv env (finalise (normalise ctxt env x)) ++ " and " ++ 
                                     showEnv env (finalise (normalise ctxt env y)))

isSet :: Context -> Env -> Term -> TC ()
isSet ctxt env tm = isSet' (normalise ctxt env tm)
    where isSet' :: Term -> TC ()
          isSet' (Set _) = return ()
          isSet' tm = fail (showEnv env tm ++ " is not a Set")

recheck :: Context -> Env -> Term -> TC (Term, Type)
recheck ctxt env tm = check ctxt env (forget tm)

check :: Context -> Env -> Raw -> TC (Term, Type)
check ctxt env (Var n)
    | Just (i, ty) <- lookupTyEnv n env = return (P Bound n ty, ty)
    | Just (P nt n' ty) <- lookupP n ctxt = return (P nt n' ty, ty)
    | otherwise = do fail $ "No such variable " ++ show n ++ " in " ++ show (map fst env)
check ctxt env (RApp f a)
    = do (fv, fty) <- check ctxt env f
         (av, aty) <- check ctxt env a
         let fty' = normalise ctxt env fty
--          trace (showEnv env fty ++ " ===> " ++ showEnv env fty') $ 
         case fty' of
           Bind x (Pi s) t ->
               do converts ctxt env s aty
                  return (App fv av, 
                          normalise ctxt env (Bind x (Let aty av) t))
           t -> fail "Can't apply a non-function type"
check ctxt env (RSet i) = return (Set i, Set i) -- LATER: (i+1))
check ctxt env (RBind n b sc)
    = do b' <- checkBinder b
         (scv, sct) <- check ctxt ((n, b'):env) sc
         discharge n b' (pToV n scv) (pToV n sct)
  where checkBinder (Lam t)
          = do (tv, tt) <- check ctxt env t
               let tv' = normalise ctxt env tv
               let tt' = normalise ctxt env tt
               isSet ctxt env tt'
               return (Lam tv')
        checkBinder (Pi t)
          = do (tv, tt) <- check ctxt env t
               let tv' = normalise ctxt env tv
               let tt' = normalise ctxt env tt
               isSet ctxt env tt'
               return (Pi tv')
        checkBinder (Let t v)
          = do (tv, tt) <- check ctxt env t
               (vv, vt) <- check ctxt env v
               let tv' = normalise ctxt env tv
               let tt' = normalise ctxt env tt
               converts ctxt env tv vt
               isSet ctxt env tt'
               return (Let tv' vv)
        checkBinder (NLet t v)
          = do (tv, tt) <- check ctxt env t
               (vv, vt) <- check ctxt env v
               let tv' = normalise ctxt env tv
               let tt' = normalise ctxt env tt
               converts ctxt env tv vt
               isSet ctxt env tt'
               return (NLet tv' vv)
        checkBinder (Hole t)
          = do (tv, tt) <- check ctxt env t
               let tv' = normalise ctxt env tv
               let tt' = normalise ctxt env tt
               isSet ctxt env tt'
               return (Hole tv')
        checkBinder (Guess t v)
          = do (tv, tt) <- check ctxt env t
               (vv, vt) <- check ctxt env v
               let tv' = normalise ctxt env tv
               let tt' = normalise ctxt env tt
               converts ctxt env tv vt
               isSet ctxt env tt'
               return (Guess tv' vv)
        checkBinder (PVar t)
          = do (tv, tt) <- check ctxt env t
               let tv' = normalise ctxt env tv
               let tt' = normalise ctxt env tt
               isSet ctxt env tt'
               return (PVar tv')

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
        discharge n (Guess t v) scv sct
          = do -- A hole can't appear in the type of its scope
               checkNotHoley 0 sct
               return (Bind n (Guess t v) scv, sct)
        discharge n (PVar t) scv sct
          = return (Bind n (PVar t) scv, sct)

        checkNotHoley i (V v) 
            | v == i = fail "You can't put a hole where a hole don't belong"
        checkNotHoley i (App f a) = do checkNotHoley i f
                                       checkNotHoley i a
        checkNotHoley i (Bind n b sc) = checkNotHoley (i+1) sc
        checkNotHoley _ _ = return ()

pToV :: Eq n => n -> TT n -> TT n
pToV n = pToV' 0 where
    pToV' i (P _ x _) | n == x = V i
    pToV' i (Bind x b sc)
                  | n == x    = Bind x (fmap (pToV' i) b) sc
                  | otherwise = Bind x (fmap (pToV' i) b) (pToV' (i+1) sc)
    pToV' i (App f a) = App (pToV' i f) (pToV' i a)
    pToV' i t = t

vToP :: TT n -> TT n
vToP = vToP' [] where
    vToP' env (V i) = let (n, b) = (env !! i) in
                          P Bound n (binderTy b)
    vToP' env (Bind n b sc) = let b' = fmap (vToP' env) b in
                                  Bind n b' (vToP' ((n, b'):env) sc)
    vToP' env (App f a) = App (vToP' env f) (vToP' env a)
    vToP' env t = t

instantiate :: TT n -> TT n -> TT n
instantiate e = subst 0 where
    subst i (V x) | i == x = e
    subst i (Bind x b sc) = Bind x (fmap (subst i) b) (subst (i+1) sc)
    subst i (App f a) = App (subst i f) (subst i a)
    subst i t = t

finalise :: Eq n => TT n -> TT n
finalise (Bind x b sc) = Bind x (fmap finalise b) (pToV x (finalise sc))
finalise (App f a) = App (finalise f) (finalise a)
finalise t = t

checkProgram :: Context -> RProgram -> TC Context
checkProgram ctxt [] = return ctxt
checkProgram ctxt ((n, RConst t) : xs) 
   = do (t', tt') <- trace (show n) $ check ctxt [] t
        isSet ctxt [] tt'
        checkProgram (addConstant n t' ctxt) xs
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
        let ctxt' = addDatatype (Data n ty' []) ctxt
        cons' <- mapM (checkCon ctxt') cons
        checkProgram (addDatatype (Data n ty' cons') ctxt) xs
  where checkCon ctxt (n, cty) = do (cty', ctyt') <- check ctxt [] cty
                                    return (n, cty')


