{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances #-}

module Evaluate(normalise) where

import Debug.Trace
import Core

normalise :: Context -> Env -> TT Name -> TT Name
normalise ctxt env t = quote 0 (eval ctxt (weakenEnv env) t)

data Value = VP NameType Name Value
           | VV Int
           | VBind Name (Binder Value) (Value -> Value)
           | VApp Value Value
           | VSet Int
           | VTmp Int

eval :: Context -> Env -> TT Name -> Value
eval ctxt genv tm = ev [] tm where
--     ev env (P Ref n ty)
--         | Just v <- lookupP n ctxt = v -- FIXME! Needs evalling
    ev env (P nt n ty)   = VP nt n (ev env ty)
    ev env (V i) | i < length env = env !! i
                 | i < length env + length genv 
                       = case genv !! (i - length env) of
                             (_, Let t v) -> ev env v
                             _            -> VV i
                 | otherwise      = error $ "Internal error: V" ++ show i
    ev env (Bind n (Let t v) sc)
           = ev (ev env v : env) sc
    ev env (Bind n b sc) = VBind n (vbind env b) (\x -> ev (x:env) sc)
       where vbind env (Lam t)  = Lam (ev env t)
             vbind env (Pi t)   = Pi (ev env t)
             vbind env (Hole t) = Hole (ev env t)
             vbind env (PVar t) = PVar (ev env t)
             vbind env (Guess v t) = Guess (ev env v) (ev env t)
    ev env (App f a) = evApply env [a] f
    ev env (Set i)   = VSet i
    
    evApply env args (App f a) = evApply env (a:args) f
    evApply env args f = apply env (ev env f) (reverse args)

    apply env (VBind n (Lam t) sc) (a:as) = apply env (sc (ev env a)) as
    apply env f                    (a:as) = unload env f (a:as)
    apply env f                    []     = f

    unload env f [] = f
    unload env f (a:as) = unload env (VApp f (ev env a)) as

quote :: Int -> Value -> TT Name
quote i (VP nt n v)    = P nt n (quote i v)
quote i (VV x)         = V x
quote i (VBind n b sc) = Bind n (quoteB b) (quote (i+1) (sc (VTmp (i+1))))
   where quoteB t = fmap (quote i) t
quote i (VApp f a)     = App (quote i f) (quote i a)
quote i (VSet u)       = Set u
quote i (VTmp x)       = V (i - x)

-- normalise ctxt env t = quote 0 (eval ctxt (evalEnv env) (hoas [] t))
--  
-- type HEnv = [(Name, Binder HTT)]
-- 
-- evalEnv :: Env -> HEnv
-- evalEnv = map (\ (n, b) -> (n, fmap (hoas []) b)) 
-- 
-- We just evaluate HOAS terms. Any de Bruijn indices will refer to higher
-- level things, so, if we remove a binder, we need to strengthen the
-- indices appropriately.

-- eval :: Context -> HEnv -> HTT -> HTT
-- eval ctxt env t = ev t where
--   ev (HP Ref n ty) 
--       | Just v <- lookupVal n ctxt = v -- FIXME! Needs evalling
--   ev (HP nt n ty) = HP nt n (ev ty)
-- {-
--   ev (HV i)
--       | i < length env = case env!! i of
--                              (n, Let t v) -> ev v
--                              _ -> HV i
--       | otherwise = HV i
-- -}
--   ev (HApp f t a) 
--       = evSpine f [(a, t)]
--     where evSpine (HApp f t a) sp = evSpine f ((a, t):sp)
--           evSpine f sp = evAp f sp
--   ev (HBind n (Let t v) sc) = weaken (-1) (ev (sc (weaken 1 (ev v))))
--   ev (HBind n b sc)
--       = HBind n (evB b) (\x -> ev (sc x))
--     where evB (Lam t) = Lam (ev t)
--           evB (Pi t) = Pi (ev t)
--           evB (Hole t) = Hole (ev t)
--           evB (Guess t v) = Guess (ev t) (ev v)
--           evB (PVar t) = PVar (ev t)
--   ev tm = tm -- Constructors + constants
-- 
--   -- TODO:add PE magic here - nothing is evaluated yet
-- 
--   evAp f sp = evAp' (ev f) sp
--   evAp' (HBind n (Lam ty) sc) ((a, t):sp)
--         = weaken (-1) (evAp' (sc (weaken 1 (ev a))) sp)
--   evAp' f sp = apply f (map (\ (a, t) -> (ev a, ev t)) sp)
-- 
--   apply f [] = f
--   apply f ((a, t):xs) = apply (HApp f t a) xs
-- 
-- -- Adjust de Bruijn indices across a term
-- 
-- weaken :: Int -> HTT -> HTT
-- weaken w (HV i) = HV (i + w)
-- weaken w (HBind n b sc) 
--    = HBind n (weakenB b) (\x -> weaken w (sc x))
--  where weakenB (Lam t)     = Lam (weaken w t)
--        weakenB (Pi t)      = Pi (weaken w t)
--        weakenB (Let t v)   = Let (weaken w t) (weaken w v)
--        weakenB (Hole t)    = Hole (weaken w t)
--        weakenB (Guess t v) = Guess (weaken w t) (weaken w v)
--        weakenB (PVar t)    = PVar (weaken w t)
-- weaken w (HApp f t a) = HApp (weaken w f) (weaken w t) (weaken w a)
-- weaken w tm = tm
-- 
-- quote :: Int -> HTT -> TT Name
-- quote env (HP nt n t) = P nt n (quote env t)
-- quote env (HV i) = V i
-- quote env (HBind n b sc)
--    = Bind n (quoteB b) (quote (env+1) (sc (HTmp (env+1))))
--   where quoteB (Lam t)     = Lam (quote env t)
--         quoteB (Pi t)      = Pi (quote env t)
--         quoteB (Let t v)   = Let (quote env t) (quote env v)
--         quoteB (Hole t)    = Hole (quote env t)
--         quoteB (Guess t v) = Guess (quote env t) (quote env v)
--         quoteB (PVar t)    = PVar (quote env t)
-- quote env (HApp f t a) = App (quote env f) (quote env t) (quote env a)
-- quote env (HSet i) = Set i
-- quote env (HTmp i) = V (env-i)
