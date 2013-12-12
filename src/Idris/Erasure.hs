module Idris.Erasure
    ( findUnusedArgs
    ) where

import Idris.AbsSyntax

import Idris.Core.CaseTree
import Idris.Core.TT

import Control.Applicative
import Control.Monad.State
import Data.Maybe
import Data.List
import qualified Data.Set as S

findUnusedArgs :: [Name] -> Idris ()
findUnusedArgs = mapM_ (\n -> withContext_ idris_callgraph n $ traceUnused n)

traceUnused :: Name -> CGInfo -> Idris ()
traceUnused n (CGInfo args calls scg usedns _) = do
    logLvl 3 $ show n ++ " used TRACE: " ++ show fargs
    recused <- recUsed . idris_callgraph <$> getIState
    let fused = nub $ usedns ++ recused
    logLvl 1 $ show n ++ " used args: " ++ show fused
    let unused = findIndices (not . (`elem` fused)) args
    logLvl 1 $ show n ++ " unused args: " ++ show (args, unused)
    addToCG n (CGInfo args calls scg usedns unused) -- updates
  where
    fargs = concatMap (getFargpos calls) (zip args [0..])
    recUsed cg = [n | (n, i, (g,j)) <- fargs, used cg [(n,i)] g j]

used :: Ctxt CGInfo -> [(Name, Int)] -> Name -> Int -> Bool
used cg path g j
   | (g, j) `elem` path = False -- cycle, never used on the way
   | otherwise = case lookupCtxt g cg of
        [CGInfo args calls scg usedns unused] ->
            if j >= length args
              then True -- overapplied, assume used
              else
                --logLvl 5 $ (show ((g, j) : path))
                let directuse = args!!j `elem` usedns in
                let garg = getFargpos calls (args!!j, j) in
                --logLvl 5 $ show (g, j, garg)
                let recused = map getUsed garg in
                -- used on any route from here, or not used recursively
                (directuse || null recused || or recused)
        _ -> True
  where
    getUsed (argn, j, (g', j')) = used cg ((g,j):path) g' j'

getFargpos :: [(Name, [[Name]])] -> (Name, Int) -> [(Name, Int, (Name, Int))]
getFargpos calls (n, i) = concatMap (getCallArgpos n i) calls
  where
    getCallArgpos :: Name -> Int -> (Name, [[Name]]) -> [(Name, Int, (Name, Int))]
    getCallArgpos n i (g, args) = mapMaybe (getOne g) (zip [0..] args)
    
    getOne :: Name -> (Int, [Name]) -> Maybe (Name, Int, (Name, Int))
    getOne g (j, xs)
        | n `elem` xs = Just (n, i, (g, j))
        | otherwise   = Nothing

