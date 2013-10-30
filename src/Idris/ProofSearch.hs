module Idris.ProofSearch(trivial, proofSearch) where

import Core.Elaborate hiding (Tactic(..))
import Core.TT
import Core.Evaluate
import Core.CaseTree
import Core.Typecheck

import Idris.AbsSyntax
import Idris.Delaborate
import Idris.Error

import Control.Monad
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

proofSearch :: (PTerm -> ElabD ()) -> Maybe Name -> Name -> IState -> ElabD ()
proofSearch elab fn nroot ist = psRec maxDepth where
    maxDepth = 10
  
    psRec 0 = fail "Maximum depth reached"
    psRec d = try' (trivial elab ist)
                   (try' (try' (resolveByCon (d - 1)) (resolveByLocals (d - 1))
                               True)
             -- if all else fails, make a new metavariable
                         (do attack; defer nroot; solve) True) True

    getFn d Nothing = []
    getFn d (Just f) | d < maxDepth-1 = [f]
                     | otherwise = []

    resolveByCon d 
        = do t <- goal
             let (f, _) = unApply t
             case f of
                P _ n _ -> case lookupCtxt n (idris_datatypes ist) of
                               [t] -> tryCons d (con_names t ++ getFn d fn)
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
                                   (psRec d) "proof search local apply"

    -- Like type class resolution, but searching with constructors
    tryCon d n
       = do let imps = case lookupCtxtName n (idris_implicits ist) of
                            [] -> []
                            [args] -> map isImp (snd args)
            ps <- get_probs
            args <- apply (Var n) imps
            ps' <- get_probs
            when (length ps < length ps') $ fail "Can't apply constructor"
            mapM_ (\ (_, h) -> do focus h
                                  psRec d)
                  (filter (\ (x, y) -> not x) (zip (map fst imps) args))
            solve
    
    isImp (PImp p _ _ _ _ _) = (True, p)
    isImp arg = (False, priority arg)
