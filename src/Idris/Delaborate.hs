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
    de env (Bind n (Pi ty) sc)  = PPi expl n (de env ty) (de (n:env) sc)
    de env (Bind n (Let ty val) sc) 
        = PLet n (de env ty) (de env val) (de (n:env) sc)
    de env (Bind n _ sc) = de (n:env) sc
    de env (Constant i) = PConstant i
    de env (Set i) = PSet 

    deFn env (App f a) args = deFn env f (a:args)
    deFn env (P _ n _) [l,r]     | n == pairTy  = PPair un (de env l) (de env r)
                                 | n == eqCon   = PRefl un
    deFn env (P _ n _) [_,_,l,r] | n == pairCon = PPair un (de env l) (de env r)
                                 | n == eqTy    = PEq un (de env l) (de env r)
    deFn env (P _ n _) args = mkPApp n (map (de env) args)
    deFn env f args = PApp un (de env f) (map pexp (map (de env) args))

    mkPApp n args 
        | Just imps <- lookupCtxt n (idris_implicits ist)
            = PApp un (PRef un n) (zipWith imp (imps ++ repeat (pexp undefined)) args)
        | otherwise = PApp un (PRef un n) (map pexp args)

    imp (PImp l n _) arg = PImp l n arg
    imp (PExp l _)   arg = PExp l arg

pshow :: IState -> Err -> String
pshow i (Msg s) = s
pshow i (CantUnify x y e) = "Can't unify " ++ show (delab i x)
                            ++ " with " ++ show (delab i y) 
                            -- ++ "\n\t(" ++ pshow i e ++ ")"
pshow i (At f e) = show f ++ ":" ++ pshow i e

