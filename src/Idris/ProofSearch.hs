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

cantSolveGoal :: ElabD a
cantSolveGoal = do g <- goal
                   env <- get_env
                   lift $ tfail $
                      CantSolveGoal g (map (\(n,b) -> (n, binderTy b)) env) 

proofSearch :: Bool -> -- recursive search (False for 'refine') 
               Bool -> -- invoked from a tactic proof. If so, making
                       -- new metavariables is meaningless, and there shoudl
                       -- be an error reported instead.
               Bool -> -- ambiguity ok
               Bool -> -- defer on failure
               Int -> -- maximum depth
               (PTerm -> ElabD ()) -> Maybe Name -> Name -> [Name] ->
               IState -> ElabD ()
proofSearch False fromProver ambigok deferonfail depth elab _ nroot [fn] ist
       = do -- get all possible versions of the name, take the first one that
            -- works
            let all_imps = lookupCtxtName fn (idris_implicits ist)
            tryAllFns all_imps
  where
    -- if nothing worked, make a new metavariable
    tryAllFns [] | fromProver = cantSolveGoal  
    tryAllFns [] = do attack; defer [] nroot; solve
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
                                              attack; defer [] nroot; solve) 
                                 (hs' \\ hs)
--                                  (filter (\ (x, y) -> not x) (zip (map fst imps) args))
                             solve

    isImp (PImp p _ _ _ _) = (True, p)
    isImp arg = (True, priority arg) -- try to get all of them by unification
proofSearch rec fromProver ambigok deferonfail maxDepth elab fn nroot hints ist 
       = do compute
            ty <- goal
            argsok <- conArgsOK ty
            if ambigok || argsok then
               case lookupCtxt nroot (idris_tyinfodata ist) of
                    [TISolution ts] -> findInferredTy ts
                    _ -> psRec rec maxDepth []
               else autoArg (sUN "auto") -- not enough info in the type yet
  where
    findInferredTy (t : _) = elab (delab ist (toUN t)) 

    conArgsOK ty
       = let (f, as) = unApply ty in
         case f of
              P _ n _ -> case lookupCtxt n (idris_datatypes ist) of
                              [t] -> do rs <- mapM (conReady as) (con_names t)
                                        return (and rs)
                              _ -> fail "Ambiguous name"
              TType _ -> return True
              _ -> fail "Not a data type"

    conReady :: [Term] -> Name -> ElabD Bool
    conReady as n 
       = case lookupTyExact n (tt_ctxt ist) of
              Just ty -> do let (_, cs) = unApply (getRetTy ty)
                            -- if any metavariables in 'as' correspond to
                            -- a constructor form in 'cs', then we're not
                            -- ready to run auto yet. Otherwise, go for it
                            hs <- get_holes
                            return $ and (map (notHole hs) (zip as cs))
              Nothing -> fail "Can't happen"

    notHole hs (P _ n _, c)
       | (P _ cn _, _) <- unApply c,
         n `elem` hs && isConName cn (tt_ctxt ist) = False
       | Constant _ <- c = not (n `elem` hs)
    notHole _ _ = True

    toUN t@(P nt (MN i n) ty) 
       | ('_':xs) <- str n = t
       | otherwise = P nt (UN n) ty
    toUN (App f a) = App (toUN f) (toUN a)
    toUN t = t

    -- psRec counts depth and the local variable applications we're under
    -- (so we don't try a pointless application of something to itself,
    -- which obviously won't work anyway but might lead us on a wild
    -- goose chase...)
    psRec _ 0 locs | fromProver = cantSolveGoal
    psRec rec 0 locs = do attack; defer [] nroot; solve --fail "Maximum depth reached"
    psRec False d locs = tryCons d locs hints 
    psRec True d locs 
                 = do compute
                      try' (trivial elab ist)
                           (try' (try' (resolveByCon (d - 1) locs) (resolveByLocals (d - 1) locs)
                                 True)
             -- if all else fails, make a new metavariable
                         (if fromProver 
                             then fail "cantSolveGoal"
                             else do attack; defer [] nroot; solve) True) True

    getFn d Nothing = []
    getFn d (Just f) | d < maxDepth-1 = [f]
                     | otherwise = []

    resolveByCon d locs
        = do t <- goal
             let (f, _) = unApply t
             case f of
                P _ n _ -> 
                   do let autohints = case lookupCtxtExact n (idris_autohints ist) of
                                           Nothing -> []
                                           Just hs -> hs
                      case lookupCtxt n (idris_datatypes ist) of
                          [t] -> tryCons d locs (hints ++ 
                                                 con_names t ++ 
                                                 autohints ++ 
                                                 getFn d fn)
                          _ -> fail "Not a data type"
                _ -> fail "Not a data type"

    -- if there are local variables which have a function type, try
    -- applying them too
    resolveByLocals d locs
        = do env <- get_env
             tryLocals d locs env

    tryLocals d locs [] = fail "Locals failed"
    tryLocals d locs ((x, t) : xs) 
       | x `elem` locs = tryLocals d locs xs
       | otherwise = try' (tryLocal d (x : locs) x t) (tryLocals d locs xs) True

    tryCons d locs [] = fail "Constructors failed"
    tryCons d locs (c : cs) = try' (tryCon d locs c) (tryCons d locs cs) True

    tryLocal d locs n t 
          = do let a = getPArity (delab ist (binderTy t))
               tryLocalArg d locs n a

    tryLocalArg d locs n 0 = elab (PRef (fileFC "prf") n)
    tryLocalArg d locs n i = simple_app False (tryLocalArg d locs n (i - 1))
                                   (psRec True d locs) "proof search local apply"

    -- Like type class resolution, but searching with constructors
    tryCon d locs n = 
         do ty <- goal
            let imps = case lookupCtxtName n (idris_implicits ist) of
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
                                  aty <- goal
                                  psRec True d locs) 
                  (filter (\ (x, y) -> not x) (zip (map fst imps) args))
            solve

    isImp (PImp p _ _ _ _) = (True, p)
    isImp arg = (False, priority arg) 

