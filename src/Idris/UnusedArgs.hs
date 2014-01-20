module Idris.UnusedArgs where

import Idris.AbsSyntax

import Idris.Core.CaseTree
import Idris.Core.TT

import Control.Monad.State
import Data.Maybe
import Data.List

findUnusedArgs :: [Name] -> Idris ()
findUnusedArgs ns = mapM_ traceUnused ns

traceUnused :: Name -> Idris ()
traceUnused n
   = do i <- getIState
        case lookupCtxt n (idris_callgraph i) of
          [CGInfo args calls scg usedns _] ->
                do let argpos = zip args [0..]
                   let fargs = concatMap (getFargpos calls) argpos
                   logLvl 3 $ show n ++ " used TRACE: " ++ show fargs
                   recused <- mapM (\ (argn, i, (g, j)) ->
                                        do u <- used [(n, i)] g j
                                           return (argn, u)) fargs
                   logLvl 4 $ show n ++ " recused TRACE: " ++ show recused
                   let fused = nub $ usedns ++ map fst (filter snd recused)
                   logLvl 1 $ show n ++ " used args: " ++ show fused
                   let unusedpos = mapMaybe (getUnused fused) (zip [0..] args)
                   logLvl 1 $ show n ++ " unused args: " ++ show (args, unusedpos)
                   addToCG n (CGInfo args calls scg usedns unusedpos) -- updates
          _ -> return ()
  where
    getUnused fused (i,n) | n `elem` fused = Nothing
                          | otherwise = Just i

used :: [(Name, Int)] -> Name -> Int -> Idris Bool
used path g j
   | (g, j) `elem` path = return False -- cycle, never used on the way
   | otherwise
       = do logLvl 5 $ (show ((g, j) : path))
            i <- getIState
            case lookupCtxt g (idris_callgraph i) of
               [CGInfo args calls scg usedns unused] ->
                  if (j >= length args)
                    then -- overapplied, assume used
                         return True
                    else do let directuse = args!!j `elem` usedns
                            let garg = getFargpos calls (args!!j, j)
                            logLvl 5 $ show (g, j, garg)
                            recused <- mapM (\ (argn, j, (g', j')) ->
                                           used ((g,j):path) g' j') garg
                            -- used on any route from here, or not used recursively
                            return (directuse || or recused)
               _ -> return True -- no definition, assume used

getFargpos :: [(Name, [[Name]])] -> (Name, Int) -> [(Name, Int, (Name, Int))]
getFargpos calls (n, i) = concatMap (getCallArgpos n i) calls
   where getCallArgpos :: Name -> Int -> (Name, [[Name]]) ->
                          [(Name, Int, (Name, Int))]
         getCallArgpos n i (g, args)
               = let argpos = zip [0..] args in
                     mapMaybe (\ (j, xs) -> if n `elem` xs then Just (n, i, (g, j))
                                                           else Nothing) argpos

