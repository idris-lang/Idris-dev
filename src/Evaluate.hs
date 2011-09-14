{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances #-}

module Evaluate(normalise) where

import Debug.Trace
import Core

normalise :: Context -> TT Name -> TT Name
normalise ctxt t = quote 0 (eval ctxt (hoas [] t))

-- We just evaluate HOAS terms. Any de Bruijn indices will refer to higher
-- level things, so, if we remove a binder, we need to strengthen the
-- indices appropriately.

eval :: Context -> HTT -> HTT
eval ctxt t = ev t where
  ev (HP Ref n ty) 
      | Just v <- lookupVal n ctxt = v -- FIXME! Needs evalling
  ev (HP nt n ty) = HP nt n (ev ty)
  ev (HApp f t a) 
      = evSpine f [(a, t)]
    where evSpine (HApp f t a) sp = evSpine f ((a, t):sp)
          evSpine f sp = evAp f sp
  ev (HBind n (Let t v) sc) = weaken (-1) (ev (sc (weaken 1 (ev v))))
  ev (HBind n b sc)
      = HBind n (evB b) (\x -> ev (sc x))
    where evB (Lam t) = Lam (ev t)
          evB (Pi t) = Pi (ev t)
          evB (Hole t) = Hole (ev t)
          evB (Guess t v) = Guess (ev t) (ev v)
          evB (PVar t) = PVar (ev t)
  ev tm = tm -- Constructors + constants

  -- TODO:add PE magic here - nothing is evaluated yet

  evAp f sp = evAp' (ev f) sp
  evAp' (HBind n (Lam ty) sc) ((a, t):sp)
        = weaken (-1) (evAp' (sc (weaken 1 (ev a))) sp)
  evAp' f sp = apply f (map (\ (a, t) -> (ev a, ev t)) sp)

  apply f [] = f
  apply f ((a, t):xs) = apply (HApp f t a) xs

-- Adjust de Bruijn indices across a term

weaken :: Int -> HTT -> HTT
weaken w (HV i) = HV (i + w)
weaken w (HBind n b sc) 
   = HBind n (weakenB b) (\x -> weaken w (sc x))
 where weakenB (Lam t)     = Lam (weaken w t)
       weakenB (Pi t)      = Pi (weaken w t)
       weakenB (Let t v)   = Let (weaken w t) (weaken w v)
       weakenB (Hole t)    = Hole (weaken w t)
       weakenB (Guess t v) = Guess (weaken w t) (weaken w v)
       weakenB (PVar t)    = PVar (weaken w t)
weaken w (HApp f t a) = HApp (weaken w f) (weaken w t) (weaken w a)
weaken w tm = tm

quote :: Int -> HTT -> TT Name
quote env (HP nt n t) = P nt n (quote env t)
quote env (HV i) = V i
quote env (HBind n b sc)
   = Bind n (quoteB b) (quote (env+1) (sc (HTmp (env+1))))
  where quoteB (Lam t)     = Lam (quote env t)
        quoteB (Pi t)      = Pi (quote env t)
        quoteB (Let t v)   = Let (quote env t) (quote env v)
        quoteB (Hole t)    = Hole (quote env t)
        quoteB (Guess t v) = Guess (quote env t) (quote env v)
        quoteB (PVar t)    = PVar (quote env t)
quote env (HApp f t a) = App (quote env f) (quote env t) (quote env a)
quote env (HSet i) = Set i
quote env (HTmp i) = V (env-i)
