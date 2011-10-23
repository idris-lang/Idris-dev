{-# LANGUAGE PatternGuards #-}

module Idris.Delaborate where

-- Convert core TT back into high level syntax, primarily for display
-- purposes.

import Idris.AbsSyntax
import Core.TT

import Debug.Trace

delab :: IState -> Term -> PTerm
delab ist tm = de [] tm
  where
    un = FC "(val)" 0

    de env (App f a) = deFn env f [a]
    de env (V i)     | i < length env = PRef un (env!!i)
                     | otherwise = PRef un (UN ["v" ++ show i ++ ""])
    de env (P _ n _) | n == unitTy = PTrue un
                     | n == unitCon = PTrue un
                     | n == falseTy = PFalse un
                     | otherwise = PRef un n
    de env (Bind n (Lam ty) sc) = PLam n (de env ty) (de (n:env) sc)
    de env (Bind n (Pi ty) sc)  = PPi Exp n (de env ty) (de (n:env) sc)
    de env (Bind n (Let ty val) sc) 
        = PLet n (de env ty) (de env val) (de (n:env) sc)
    de env (Bind n _ sc) = de (n:env) sc
    de env (Constant i) = PConstant i
    de env (Set i) = PSet 

    deFn env (App f a) args = deFn env f (a:args)
    deFn env (P _ n _) [l,r]     | n == pairTy  = PPair un (de env l) (de env r)
    deFn env (P _ n _) [_,_,l,r] | n == pairCon = PPair un (de env l) (de env r)
    deFn env (P _ n _) args = mkPApp n (map (de env) args)
    deFn env f args = PApp un (de env f) (map PExp (map (de env) args))

    mkPApp n args 
        | Just imps <- lookupCtxt n (idris_implicits ist)
            = PApp un (PRef un n) (zipWith imp (imps ++ repeat (PExp undefined)) args)
        | otherwise = PApp un (PRef un n) (map PExp args)

    imp (PImp n _) arg = PImp n arg
    imp (PExp _)   arg = PExp arg

