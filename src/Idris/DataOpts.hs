{-# LANGUAGE PatternGuards #-}

module Idris.DataOpts where

-- Forcing, detagging and collapsing

import Idris.AbsSyntax
import Core.TT

import Data.List
import Data.Maybe
import Debug.Trace

-- Calculate the forceable arguments to a constructor and update the set of
-- optimisations

forceArgs :: Name -> Type -> Idris ()
-- forceArgs n t = return ()
forceArgs n t = do let fargs = force 0 t
                   i <- getIState
                   copt <- case lookupCtxt Nothing n (idris_optimisation i) of
                                 []     -> return $ Optimise False [] []
                                 (op:_) -> return op
                   let opts = addDef n (copt { forceable = fargs }) (idris_optimisation i)
                   putIState (i { idris_optimisation = opts })
                   addIBC (IBCOpt n)
                   iLOG $ "Forced: " ++ show n ++ " " ++ show fargs
  where
    force :: Int -> Term -> [Int]
    force i (Bind _ (Pi _) sc) 
        = force (i + 1) $ instantiate (P Bound (MN i "F?") Erased) sc
    force _ sc@(App f a) 
        | (_, args) <- unApply sc 
            = nub $ concatMap guarded args
    force _ _ = []

    isF (P _ (MN force "F?") _) = Just force
    isF _ = Nothing

    guarded :: Term -> [Int]
    guarded t@(App f a)
        | (P (TCon _ _) _ _, args) <- unApply t
            = mapMaybe isF args ++ concatMap guarded args
        | (P (DCon _ _) _ _, args) <- unApply t
            = mapMaybe isF args ++ concatMap guarded args
    guarded t = mapMaybe isF [t]

class Optimisable term where
    applyOpts :: term -> Idris term

-- Raw is for compile time optimisation (before type checking)
-- Term is for run time optimisation (after type checking, collapsing allowed)

instance Optimisable Raw where
    applyOpts t@(RApp f a)
        | (Var n, args) <- raw_unapply t -- MAGIC HERE
            = do i <- getIState
                 case lookupCtxt Nothing n (idris_optimisation i) of
                    (oi:_) -> return $ applyDataOpt oi n args
                    _ -> do args' <- mapM applyOpts args
                            return (raw_apply (Var n) args')
        | otherwise = do f' <- applyOpts f
                         a' <- applyOpts a
                         return (RApp f' a')
    applyOpts (RBind n b t) = do b' <- applyOpts b
                                 t' <- applyOpts t
                                 return (RBind n b' t')
    applyOpts (RForce t) = applyOpts t
    applyOpts t = return t

instance Optimisable t => Optimisable (Binder t) where
    applyOpts (Let t v) = do t' <- applyOpts t
                             v' <- applyOpts v
                             return (Let t' v')
    applyOpts b = do t' <- applyOpts (binderTy b)
                     return (b { binderTy = t' })

-- Compile time: no collapsing

applyDataOpt :: OptInfo -> Name -> [Raw] -> Raw
applyDataOpt oi n args
    = let args' = zipWith doForce (map (\x -> x `elem` (forceable oi)) [0..]) 
                                  args in
          raw_apply (Var n) args'
  where
    doForce True  a = RForce a
    doForce False a = a

