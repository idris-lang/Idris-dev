{-# LANGUAGE PatternGuards #-}

module Idris.Erasure
    ( findUnusedArgs
    ) where

import Idris.AbsSyntax
import Idris.Core.CaseTree
import Idris.Core.TT
import Idris.Core.Evaluate

import Control.Applicative
import Control.Monad.State
import Data.Maybe
import Data.List
import qualified Data.IntSet as S
import qualified Data.Map as M
import Data.IntSet (IntSet)
import Data.Map (Map)

findUsed :: Context -> Ctxt CGInfo -> [Name] -> Map Name IntSet
findUsed ctx cg ns = union $ map (findUsedDef cg . getDef ctx) ns
  where
    union :: [Map Name IntSet] -> Map Name IntSet
    union = M.unionsWith S.union

    getDef :: Context -> Name -> Def
    getDef ctx n = case lookupDef n ctx of
        [def] -> def
        [] -> error $ "erasure checker: unknown name: " ++ show n  -- TODO: fix this
        _  -> error $ "erasure checker: ambiguous name: " ++ show n  -- TODO: fix this

    findUsedDef :: Ctxt CGInfo -> Def -> Map Name IntSet
    findUsedDef cg (Function ty t  ) = M.empty
    findUsedDef cg (TyDecl   ty t  ) = M.empty
    findUsedDef cg (Operator ty n f) = M.empty
    --  ^- non-pattern-matching definitions don't contribute to usage of data
    
    findUsedDef cg (CaseOp ci ty def tot cdefs)
        -- the fst component is the list of pattern variables, which we don't use
        = findUsedSC cg M.empty (snd $ cases_compiletime cdefs)  -- TODO: or cases_runtime?

    findUsedSC :: Ctxt CGInfo -> Map Name (Name, Int) -> SC -> Map Name IntSet
    findUsedSC cg vars  ImpossibleCase     = M.empty
    findUsedSC cg vars (UnmatchedCase msg) = M.empty
    findUsedSC cg vars (Case     n alts) = undefined
    findUsedSC cg vars (ProjCase t alt) = undefined
    findUsedSC cg vars (STerm t) = undefined

findUnusedArgs :: [Name] -> Idris ()
findUnusedArgs names = do
    cg <- idris_callgraph <$> getIState
    mapM_ (process cg) names
  where
    process :: Ctxt CGInfo -> Name -> Idris ()
    process cg n = case lookupCtxt n cg of
        [x] -> do
            let unused = traceUnused cg n x 
            logLvl 1 $ show n ++ " unused: " ++ show unused
            addToCG n $ x{ unusedpos = unused }
        _ -> return ()

    traceUnused :: Ctxt CGInfo -> Name -> CGInfo -> [Int]
    traceUnused cg n (CGInfo args calls _ usedns _)
        = findIndices (not . (`elem` fused)) args
      where
        fargs   = concatMap (getFargpos calls) (zip args [0..])
        recused = [n | (n, i, (g,j)) <- fargs, used cg [(n,i)] g j]
        fused   = nub $ usedns ++ recused
        
    used :: Ctxt CGInfo -> [(Name, Int)] -> Name -> Int -> Bool
    used cg path g j
        | (g, j) `elem` path = False -- cycle, never used on the way

        | [CGInfo args calls _ usedns _] <- lookupCtxt g cg
        , j < length args  -- not overapplied
        = let directuse = args!!j `elem` usedns
              garg      = getFargpos calls (args!!j, j)
              recused   = map getUsed garg
          in directuse || null recused || or recused
          -- used on any route from here, or not used recursively

        | otherwise = True
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

