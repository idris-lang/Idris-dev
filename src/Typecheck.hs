{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances, DeriveFunctor #-}

module Typecheck where

import Control.Monad.State
import Debug.Trace

import Core
import Evaluate

data TC a = OK a
          | Error String -- TMP! Make this an informative data structure
  deriving (Eq, Functor)

instance Show a => Show (TC a) where
    show (OK x) = show x
    show (Error str) = "Error: " ++ str

-- at some point, this instance should also carry type checking options
-- (e.g. Set:Set)

instance Monad TC where
    return = OK 
    x >>= k = case x of 
                OK v -> k v
                Error e -> Error e
    fail = Error

instance MonadPlus TC where
    mzero = Error "Unknown error"
    (OK x) `mplus` _ = OK x
    _ `mplus` (OK y) = OK y
    err `mplus` _    = err

converts :: Context -> Env -> Term -> Term -> TC ()
converts ctxt env x y = if (normalise ctxt env (bindEnv env x) ==
                            normalise ctxt env (bindEnv env y))
                          then return ()
                          else fail ("Can't convert between " ++ 
                                     show x ++ " and " ++ show y)

isSet :: Term -> TC ()
isSet (Set _) = return ()
isSet tm = fail (show tm ++ " is not a Set")

check :: Context -> Env -> Raw -> TC (Term, Type)
check ctxt env (Var n)
    | Just (i, ty) <- lookupTyEnv n env = return (V i, ty)
    | Just (P nt n' ty) <- lookupP n ctxt = return (P nt n' ty, ty)
    | otherwise = do fail $ "No such variable " ++ show n
check ctxt env (RApp f a)
    = do (fv, fty) <- check ctxt env f
         (av, aty) <- check ctxt env a
         let fty' = normalise ctxt env fty
         case fty' of
           Bind x (Pi s) t ->
               do converts ctxt env s aty
                  return (App fv fty av, 
                          normalise ctxt env (Bind x (Let av aty) t))
           t -> fail "Can't apply a non-function type"
check ctxt env (RSet i) = return (Set i, Set (i+1))
check ctxt env (RBind n b sc)
    = do b' <- checkBinder b
         (scv, sct) <- check ctxt ((n, b'):env) sc
         discharge n b' scv sct
  where checkBinder (Lam t)
          = do (tv, tt) <- check ctxt env t
               let tv' = normalise ctxt env tv
               let tt' = normalise ctxt env tt
               isSet tt'
               return (Lam tv')
        checkBinder (Pi t)
          = do (tv, tt) <- check ctxt env t
               let tv' = normalise ctxt env tv
               let tt' = normalise ctxt env tt
               isSet tt'
               return (Pi tv')
        checkBinder (Let t v)
          = do (tv, tt) <- check ctxt env t
               (vv, vt) <- check ctxt env v
               let tv' = normalise ctxt env tv
               let tt' = normalise ctxt env tt
               converts ctxt env tv vt
               isSet tt'
               return (Let tv' vv)
        checkBinder (Hole t)
          = do (tv, tt) <- check ctxt env t
               let tv' = normalise ctxt env tv
               let tt' = normalise ctxt env tt
               isSet tt'
               return (Hole tv')
        checkBinder (Guess t v)
          = do (tv, tt) <- check ctxt env t
               (vv, vt) <- check ctxt env v
               let tv' = normalise ctxt env tv
               let tt' = normalise ctxt env tt
               converts ctxt env tv vt
               isSet tt'
               return (Guess tv' vv)
        checkBinder (PVar t)
          = do (tv, tt) <- check ctxt env t
               let tv' = normalise ctxt env tv
               let tt' = normalise ctxt env tt
               isSet tt'
               return (PVar tv')

        discharge n (Lam t) scv sct
          = return (Bind n (Lam t) scv, Bind n (Pi t) sct)
        discharge n (Pi t) scv sct
          = return (Bind n (Pi t) scv, sct)
        discharge n (Let t v) scv sct
          = return (Bind n (Let t v) scv, Bind n (Let t v) sct)
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
        checkNotHoley i (App f t a) = do checkNotHoley i f
                                         checkNotHoley i t
                                         checkNotHoley i a
        checkNotHoley i (Bind n b sc) = checkNotHoley (i+1) sc
        checkNotHoley _ _ = return ()

checkProgram :: Context -> RProgram -> TC Context
checkProgram ctxt [] = return ctxt
checkProgram ctxt ((n, RConst t):xs) 
   = do (t', tt') <- trace (show n) $ check ctxt [] t
        isSet tt'
        checkProgram ((n, Constant Ref t' (hoas [] t')):ctxt) xs
checkProgram ctxt ((n, RFunction (RawFun ty val)):xs)
   = do (ty', tyt') <- trace (show n) $ check ctxt [] ty
        (val', valt') <- check ctxt [] val
        isSet tyt'
        converts ctxt [] ty' valt'
        checkProgram ((n, Function (Fun ty' (hoas [] ty')
                                        val' (hoas [] val'))):ctxt) xs
