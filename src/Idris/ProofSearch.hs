{-# LANGUAGE PatternGuards #-}

module Idris.ProofSearch(trivial, trivialHoles, proofSearch) where

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
import qualified Data.Set as S
import Data.List
import Debug.Trace

-- Pass in a term elaborator to avoid a cyclic dependency with ElabTerm

trivial :: (PTerm -> ElabD ()) -> IState -> ElabD ()
trivial = trivialHoles []

trivialHoles :: [(Name, Int)] -> (PTerm -> ElabD ()) -> IState -> ElabD ()
trivialHoles ok elab ist 
                 = try' (do elab (PApp (fileFC "prf") (PRef (fileFC "prf") eqCon) [pimp (sUN "A") Placeholder False, pimp (sUN "x") Placeholder False])
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
                let badhs = hs -- filter (flip notElem holesOK) hs
                g <- goal
                -- anywhere but the top is okay for a hole, if holesOK set
                if -- all (\n -> not (n `elem` badhs)) (freeNames (binderTy b))
                   holesOK hs (binderTy b)
                   then try' (elab (PRef (fileFC "prf") x))
                             (tryAll xs) True
                   else tryAll xs
        
        holesOK hs ap@(App _ _ _)
           | (P _ n _, args) <- unApply ap
                = holeArgsOK hs n 0 args
        holesOK hs (App _ f a) = holesOK hs f && holesOK hs a
        holesOK hs (P _ n _) = not (n `elem` hs)
        holesOK hs (Bind n b sc) = holesOK hs (binderTy b) && 
                                   holesOK hs sc
        holesOK hs _ = True

        holeArgsOK hs n p [] = True
        holeArgsOK hs n p (a : as)
           | (n, p) `elem` ok = holeArgsOK hs n (p + 1) as
           | otherwise = holesOK hs a && holeArgsOK hs n (p + 1) as

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
            hs <- get_holes
            env <- get_env
            tm <- get_term
            argsok <- conArgsOK ty
            if ambigok || argsok then
               case lookupCtxt nroot (idris_tyinfodata ist) of
                    [TISolution ts] -> findInferredTy ts
                    _ -> psRec rec maxDepth [] S.empty
               else do ptm <- get_term
                       autoArg (sUN "auto") -- not enough info in the type yet
  where
    findInferredTy (t : _) = elab (delab ist (toUN t)) 

    conArgsOK ty
       = let (f, as) = unApply ty in
           case f of
              P _ n _ -> 
                let autohints = case lookupCtxtExact n (idris_autohints ist) of
                                     Nothing -> []
                                     Just hs -> hs in
                    case lookupCtxtExact n (idris_datatypes ist) of
                              Just t -> do rs <- mapM (conReady as) 
                                                      (autohints ++ con_names t)
                                           return (and rs)
                              Nothing -> -- local variable, go for it
                                    return True
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
    toUN (App s f a) = App s (toUN f) (toUN a)
    toUN t = t

    -- psRec counts depth and the local variable applications we're under
    -- (so we don't try a pointless application of something to itself,
    -- which obviously won't work anyway but might lead us on a wild
    -- goose chase...)
    -- Also keep track of the types we've proved so far in this branch
    -- (if we get back to one we've been to before, we're just in a cycle and
    -- that's no use)
    psRec :: Bool -> Int -> [Name] -> S.Set Type -> ElabD ()
    psRec _ 0 locs tys | fromProver = cantSolveGoal
    psRec rec 0 locs tys = do attack; defer [] nroot; solve --fail "Maximum depth reached"
    psRec False d locs tys = tryCons d locs tys hints 
    psRec True d locs tys
                 = do compute
                      ty <- goal
                      when (S.member ty tys) $ fail "Been here before"
                      let tys' = S.insert ty tys
                      try' (trivial elab ist)
                           (try' (try' (resolveByCon (d - 1) locs tys') 
                                       (resolveByLocals (d - 1) locs tys')
                                 True)
             -- if all else fails, make a new metavariable
                         (if fromProver 
                             then fail "cantSolveGoal"
                             else do attack; defer [] nroot; solve) True) True

    getFn d Nothing = []
    getFn d (Just f) | d < maxDepth-1 = [f]
                     | otherwise = []

    resolveByCon d locs tys
        = do t <- goal
             let (f, _) = unApply t
             case f of
                P _ n _ -> 
                   do let autohints = case lookupCtxtExact n (idris_autohints ist) of
                                           Nothing -> []
                                           Just hs -> hs
                      case lookupCtxtExact n (idris_datatypes ist) of
                          Just t -> tryCons d locs tys 
                                                   (hints ++ 
                                                    con_names t ++ 
                                                    autohints ++ 
                                                    getFn d fn)
                          Nothing -> fail "Not a data type"
                _ -> fail "Not a data type"

    -- if there are local variables which have a function type, try
    -- applying them too
    resolveByLocals d locs tys
        = do env <- get_env
             tryLocals d locs tys env

    tryLocals d locs tys [] = fail "Locals failed"
    tryLocals d locs tys ((x, t) : xs) 
       | x `elem` locs = tryLocals d locs tys xs
       | otherwise = try' (tryLocal d (x : locs) tys x t) 
                          (tryLocals d locs tys xs) True

    tryCons d locs tys [] = fail "Constructors failed"
    tryCons d locs tys (c : cs) 
        = try' (tryCon d locs tys c) (tryCons d locs tys cs) True

    tryLocal d locs tys n t 
          = do let a = getPArity (delab ist (binderTy t))
               tryLocalArg d locs tys n a

    tryLocalArg d locs tys n 0 = elab (PRef (fileFC "prf") n)
    tryLocalArg d locs tys n i 
        = simple_app False (tryLocalArg d locs tys n (i - 1))
                (psRec True d locs tys) "proof search local apply"

    -- Like type class resolution, but searching with constructors
    tryCon d locs tys n = 
         do ty <- goal
            let imps = case lookupCtxtExact n (idris_implicits ist) of
                            Nothing -> []
                            Just args -> map isImp args
            ps <- get_probs
            hs <- get_holes
            args <- map snd <$> try' (apply (Var n) imps)
                                     (match_apply (Var n) imps) True
            ps' <- get_probs
            hs' <- get_holes
            when (length ps < length ps') $ fail "Can't apply constructor"
            mapM_ (\ (_, h) -> do focus h
                                  aty <- goal
                                  psRec True d locs tys)
                  (filter (\ (x, y) -> not x) (zip (map fst imps) args))
            solve

    isImp (PImp p _ _ _ _) = (True, p)
    isImp arg = (False, priority arg) 

