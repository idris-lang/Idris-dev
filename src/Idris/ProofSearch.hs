{-# LANGUAGE PatternGuards #-}

module Idris.ProofSearch(trivial, proofSearch) where

import Idris.Core.Elaborate hiding (Tactic(..))
import Idris.Core.TT
import Idris.Core.Evaluate
import Idris.Core.CaseTree
import Idris.Core.Typecheck

import Idris.AbsSyntax
import Idris.Delaborate
import Idris.Error

import Control.Applicative ((<$>))
import Control.Monad
import Control.Monad.State.Strict
import Data.List
import Debug.Trace

-- Pass in a term elaborator to avoid a cyclic dependency with ElabTerm

trivial :: (PTerm -> ElabD ()) -> IState -> ElabD ()
trivial elab ist = try' (do elab (PRefl (fileFC "prf") Placeholder)
                            return ())
                        (do env <- get_env
                            g <- goal
                            tryAll env
                            return ()) True
      where
        tryAll []     = fail "No trivial solution"
        tryAll ((x, b):xs)
           = do -- if type of x has any holes in it, move on
                hs <- get_holes
                g <- goal
                if all (\n -> not (n `elem` hs)) (freeNames (binderTy b))
                   then try' (elab (PRef (fileFC "prf") x))
                             (tryAll xs) True
                   else tryAll xs

cantSolveGoal :: ElabD ()
cantSolveGoal = do g <- goal
                   env <- get_env
                   lift $ tfail $
                      CantSolveGoal g (map (\(n,b) -> (n, binderTy b)) env) 

proofSearch :: Bool -> 
               Bool -> -- invoked from a tactic proof. If so, making
                       -- new metavariables is meaningless, and there shoudl
                       -- be an error reported instead.
               Int -> -- maximum depth
               (PTerm -> ElabD ()) -> Maybe Name -> Name -> [Name] ->
               IState -> ElabD ()
proofSearch False fromProver depth elab _ nroot [fn] ist
       = do -- get all possible versions of the name, take the first one that
            -- works
            let all_imps = lookupCtxtName fn (idris_implicits ist)
            tryAllFns all_imps
  where
    -- if nothing worked, make a new metavariable
    tryAllFns [] | fromProver = cantSolveGoal  
    tryAllFns [] = do attack; defer nroot; solve
    tryAllFns (f : fs) = try' (tryFn f) (tryAllFns fs) True

    tryFn (f, args) = do let imps = map isImp args
                         ps <- get_probs
                         hs <- get_holes
                         args <- map snd <$> try' (apply (Var f) imps)
                                                  (match_apply (Var f) imps) True
                         ps' <- get_probs
--                          when (length ps < length ps') $ fail "Can't apply constructor"
                         -- Make metavariables for new holes 
                         hs' <- get_holes
                         ptm <- get_term
                         if fromProver then cantSolveGoal
                           else do
                             mapM_ (\ h -> do focus h
                                              attack; defer nroot; solve) 
                                 (hs' \\ hs)
--                                  (filter (\ (x, y) -> not x) (zip (map fst imps) args))
                             solve

    isImp (PImp p _ _ _ _) = (True, p)
    isImp arg = (True, priority arg) -- try to get all of them by unification
proofSearch rec fromProver maxDepth elab fn nroot hints ist 
       = case lookupCtxt nroot (idris_tyinfodata ist) of
              [TISolution ts] -> findInferredTy ts
              _ -> psRec rec maxDepth
  where
    findInferredTy (t : _) = elab (delab ist (toUN t)) 

    toUN t@(P nt (MN i n) ty) 
       | ('_':xs) <- str n = t
       | otherwise = P nt (UN n) ty
    toUN (App f a) = App (toUN f) (toUN a)
    toUN t = t

    psRec _ 0 | fromProver = cantSolveGoal
    psRec rec 0 = do attack; defer nroot; solve --fail "Maximum depth reached"
    psRec False d = tryCons d hints 
    psRec True d = try' (trivial elab ist)
                        (try' (try' (resolveByCon (d - 1)) (resolveByLocals (d - 1))
                              True)
             -- if all else fails, make a new metavariable
                         (if fromProver 
                             then cantSolveGoal
                             else do attack; defer nroot; solve) True) True

    getFn d Nothing = []
    getFn d (Just f) | d < maxDepth-1 = [f]
                     | otherwise = []

    resolveByCon d
        = do t <- goal
             let (f, _) = unApply t
             case f of
                P _ n _ -> case lookupCtxt n (idris_datatypes ist) of
                               [t] -> tryCons d (hints ++ con_names t ++
                                                                getFn d fn)
                               _ -> fail "Not a data type"
                _ -> fail "Not a data type"

    -- if there are local variables which have a function type, try
    -- applying them too
    resolveByLocals d
        = do env <- get_env
             tryLocals d env

    tryLocals d [] = fail "Locals failed"
    tryLocals d ((x, t) : xs) = try' (tryLocal d x t) (tryLocals d xs) True

    tryCons d [] = fail "Constructors failed"
    tryCons d (c : cs) = try' (tryCon d c) (tryCons d cs) True

    tryLocal d n t = do let a = getPArity (delab ist (binderTy t))
                        tryLocalArg d n a

    tryLocalArg d n 0 = elab (PRef (fileFC "prf") n)
    tryLocalArg d n i = simple_app (tryLocalArg d n (i - 1))
                                   (psRec True d) "proof search local apply"

    -- Like type class resolution, but searching with constructors
    tryCon d n =
         do let imps = case lookupCtxtName n (idris_implicits ist) of
                            [] -> []
                            [args] -> map isImp (snd args)
                            _ -> fail "Ambiguous name"
            ps <- get_probs
            hs <- get_holes
            args <- map snd <$> try' (apply (Var n) imps)
                                     (match_apply (Var n) imps) True
            ps' <- get_probs
            hs' <- get_holes
            when (length ps < length ps') $ fail "Can't apply constructor"
            mapM_ (\ (_, h) -> do focus h
                                  psRec True d) 
                  (filter (\ (x, y) -> not x) (zip (map fst imps) args))
            solve

    isImp (PImp p _ _ _ _) = (True, p)
    isImp arg = (False, priority arg) 

