-- | Check universe constraints.
module Idris.Core.Constraints(ucheck) where

import Idris.Core.TT
import Idris.Core.Typecheck

import Control.Applicative
import Control.Arrow
import Control.Monad.Error
import Control.Monad.RWS
import Control.Monad.State
import Data.List
import Data.Maybe
import qualified Data.Map as M

import Debug.Trace

-- | Check that a list of universe constraints can be satisfied.
ucheck :: [(UConstraint, FC)] -> TC ()
ucheck cs = acyclic rels (map fst (M.toList rels))
  where lhs (ULT l _) = l
        lhs (ULE l _) = l
        rels = mkRels cs M.empty

type Relations = M.Map UExp [(UConstraint, FC)]

mkRels :: [(UConstraint, FC)] -> Relations -> Relations
mkRels [] acc = acc
mkRels ((c, f) : cs) acc
    | not (ignore c)
       = case M.lookup (lhs c) acc of
              Nothing -> mkRels cs (M.insert (lhs c) [(c,f)] acc)
              Just rs -> mkRels cs (M.insert (lhs c) ((c,f):rs) acc)
    | otherwise = mkRels cs acc
  where lhs (ULT l _) = l
        lhs (ULE l _) = l
        ignore (ULE l r) = l == r
        ignore _ = False


acyclic :: Relations -> [UExp] -> TC ()
acyclic r cvs = checkCycle (fileFC "root") r [] 0 cvs
  where
    checkCycle :: FC -> Relations -> [(UExp, FC)] -> Int -> [UExp] -> TC ()
    checkCycle fc r path inc [] = return ()
    checkCycle fc r path inc (c : cs)
        = do check fc path inc c
             -- Remove c from r since we know there's no cycles now
             let r' = M.insert c [] r
             checkCycle fc r' path inc cs

    check fc path inc (UVar x) | x < 0 = return ()
    check fc path inc cv
        | inc > 0 && cv `elem` map fst path
            = Error $ At fc UniverseError
                -- FIXME: Make informative
                -- e.g. (Msg ("Cycle: " ++ show cv ++ ", " ++ show path))
        -- if we reach a cycle but we're at the same universe level, it's
        -- fine, because they must all be equal, so stop.
        | inc == 0 && cv `elem` map fst path
            = return ()
        | otherwise = case M.lookup cv r of
                            Nothing       -> return ()
                            Just cs -> mapM_ (next ((cv, fc):path) inc) cs

    next path inc (ULT l r, fc) = check fc path (inc + 1) r
    next path inc (ULE l r, fc) = check fc path inc r
