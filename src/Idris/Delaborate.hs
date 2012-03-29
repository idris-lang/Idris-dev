{-# LANGUAGE PatternGuards #-}

module Idris.Delaborate where

-- Convert core TT back into high level syntax, primarily for display
-- purposes.

import Idris.AbsSyntax
import Core.TT

import Debug.Trace

delab :: IState -> Term -> PTerm
delab i tm = delab' i tm False

delab' :: IState -> Term -> Bool -> PTerm
delab' ist tm fullname = de [] tm
  where
    un = FC "(val)" 0

    de env (App f a) = deFn env f [a]
    de env (V i)     | i < length env = PRef un (snd (env!!i))
                     | otherwise = PRef un (UN ("v" ++ show i ++ ""))
    de env (P _ n _) | n == unitTy = PTrue un
                     | n == unitCon = PTrue un
                     | n == falseTy = PFalse un
                     | Just n' <- lookup n env = PRef un n'
                     | otherwise = PRef un (dens n)
    de env (Bind n (Lam ty) sc) = PLam n (de env ty) (de ((n,n):env) sc)
    de env (Bind n (Pi ty) sc)  = PPi expl n (de env ty) (de ((n,n):env) sc)
    de env (Bind n (Let ty val) sc) 
        = PLet n (de env ty) (de env val) (de ((n,n):env) sc)
    de env (Bind n (Hole ty) sc) = de ((n, UN "[__]"):env) sc
    de env (Bind n (Guess ty val) sc) = de ((n, UN "[__]"):env) sc
    de env (Bind n _ sc) = de ((n,n):env) sc
    de env (Constant i) = PConstant i
    de env Erased = Placeholder
    de env (Set i) = PSet 

    dens x | fullname = x
    dens ns@(NS n _) = case lookupCtxt Nothing n (idris_implicits ist) of
                              [_] -> n -- just one thing
                              _ -> ns
    dens n = n

    deFn env (App f a) args = deFn env f (a:args)
    deFn env (P _ n _) [l,r]     | n == pairTy  = PPair un (de env l) (de env r)
                                 | n == eqCon   = PRefl un
                                 | n == UN "lazy" = de env r
    deFn env (P _ n _) [ty, Bind x (Lam _) r]
                                 | n == UN "Exists" 
                                       = PDPair un (PRef un x) (de env ty)
                                                   (de env (instantiate (P Bound x ty) r))
    deFn env (P _ n _) [_,_,l,r] | n == pairCon = PPair un (de env l) (de env r)
                                 | n == eqTy    = PEq un (de env l) (de env r)
                                 | n == UN "Ex_intro" = PDPair un (de env l) Placeholder
                                                                  (de env r)
    deFn env (P _ n _) args = mkPApp (dens n) (map (de env) args)
    deFn env f args = PApp un (de env f) (map pexp (map (de env) args))

    mkPApp n args 
        | [imps] <- lookupCtxt Nothing n (idris_implicits ist)
            = PApp un (PRef un n) (zipWith imp (imps ++ repeat (pexp undefined)) args)
        | otherwise = PApp un (PRef un n) (map pexp args)

    imp (PImp p l n _) arg = PImp p l n arg
    imp (PExp p l _)   arg = PExp p l arg
    imp (PConstraint p l _) arg = PConstraint p l arg
    imp (PTacImplicit p l n sc _) arg = PTacImplicit p l n sc arg

pshow :: IState -> Err -> String
pshow i (Msg s) = s
pshow i (CantUnify x y e s) 
    = "Can't unify " ++ show (delab i x)
        ++ " with " ++ show (delab i y) ++
--         " (" ++ show x ++ " and " ++ show y ++ ") " ++
        case e of
            Msg "" -> ""
            _ -> "\n\nSpecifically:\n\t " ++ pshow i e 
pshow i (NotInjective p x y) = "Can't verify injectivity of " ++ show (delab i p) ++
                               " when unifying " ++ show (delab i x) ++ " and " ++ 
                                                    show (delab i y)
pshow i (CantResolve c) = "Can't resolve type class " ++ show (delab i c)
pshow i (NoSuchVariable n) = "No such variable " ++ show n
pshow i (IncompleteTerm t) = "Incomplete term " ++ show (delab i t)
pshow i UniverseError = "Universe inconsistency"
pshow i ProgramLineComment = "Program line next to comment"
pshow i (At f e) = show f ++ ":" ++ pshow i e

