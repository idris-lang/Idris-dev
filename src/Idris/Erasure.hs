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

findUnusedArgs :: [Name] -> Idris ()
findUnusedArgs ns = mapM_ traceUnused ns

traceUnused :: Name -> Idris ()
traceUnused n = withContext_ idris_callgraph n $
    \(CGInfo args calls scg usedns _) -> do
        let argpos = zip args [0..]
        let fargs = concatMap (getFargpos calls) argpos
        logLvl 3 $ show n ++ " used TRACE: " ++ show fargs
        recused <- mapM getUsed fargs
        let fused = nub $ usedns ++ map fst (filter snd recused)
        logLvl 1 $ show n ++ " used args: " ++ show fused
        let unusedpos = mapMaybe (getUnused fused) (zip [0..] args)
        logLvl 1 $ show n ++ " unused args: " ++ show (args, unusedpos)
        addToCG n (CGInfo args calls scg usedns unusedpos) -- updates
  where
    getUsed (argn, i, (g, j)) = (,) argn <$> used [(n,i)] g j
    getUnused fused (i,n)
        | n `elem` fused = Nothing
        | otherwise      = Just i

used :: [(Name, Int)] -> Name -> Int -> Idris Bool
used path g j
   | (g, j) `elem` path = return False -- cycle, never used on the way
   | otherwise          = withContext idris_callgraph g True $
        \(CGInfo args calls scg usedns unused) ->
            if j >= length args
              then return True -- overapplied, assume used
              else do
                logLvl 5 $ (show ((g, j) : path))
                let directuse = args!!j `elem` usedns
                let garg = getFargpos calls (args!!j, j)
                logLvl 5 $ show (g, j, garg)
                recused <- mapM getUsed garg
                -- used on any route from here, or not used recursively
                return (directuse || null recused || or recused)
  where
    getUsed (argn, j, (g', j')) = used ((g,j):path) g' j'

getFargpos :: [(Name, [[Name]])] -> (Name, Int) -> [(Name, Int, (Name, Int))]
getFargpos calls (n, i) = concatMap (getCallArgpos n i) calls
  where
    getCallArgpos :: Name -> Int -> (Name, [[Name]]) -> [(Name, Int, (Name, Int))]
    getCallArgpos n i (g, args) = mapMaybe (getOne g) (zip [0..] args)
    
    getOne :: Name -> (Int, [Name]) -> Maybe (Name, Int, (Name, Int))
    getOne g (j, xs)
        | n `elem` xs = Just (n, i, (g, j))
        | otherwise   = Nothing

