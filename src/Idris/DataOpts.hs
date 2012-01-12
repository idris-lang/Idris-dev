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
forceArgs n t = do let fargs = force 0 t
                   i <- getIState
                   copt <- case lookupCtxt Nothing n (idris_optimisation i) of
                                 []     -> return $ Optimise False [] []
                                 (op:_) -> return op
                   let opts = addDef n (copt { forceable = fargs }) (idris_optimisation i)
                   putIState (i { idris_optimisation = opts })
                   addIBC (IBCOpt n)
                   iLOG $ "Forced: " ++ show n ++ " " ++ show fargs ++ "\n   from " ++
                          show t
  where
    force :: Int -> Term -> [Int]
    force i (Bind _ (Pi _) sc) 
        = force (i + 1) $ instantiate (P Bound (MN i "?") Erased) sc
    force _ sc@(App f a) 
        | (_, args) <- unApply sc 
            = nub $ concatMap guarded args
    force _ _ = []

    isF (P _ (MN force "?") _) = Just force
    isF _ = Nothing

    guarded :: Term -> [Int]
    guarded t@(App f a)
        | (P (TCon _ _) _ _, args) <- unApply t
            = mapMaybe isF args ++ concatMap guarded args
        | (P (DCon _ _) _ _, args) <- unApply t
            = mapMaybe isF args ++ concatMap guarded args
    guarded t = mapMaybe isF [t]

-- Calculate whether a collection of constructors is collapsible

collapseCons :: Name -> [(Name, Type)] -> Idris ()
collapseCons ty cons = 
                do i <- getIState
                   return ()

class Optimisable term where
    applyOpts :: term -> Idris term

instance (Optimisable a, Optimisable b) => Optimisable (a, b) where
    applyOpts (x, y) = do x' <- applyOpts x
                          y' <- applyOpts y
                          return (x', y')

instance Optimisable a => Optimisable [a] where
    applyOpts = mapM applyOpts

-- Raw is for compile time optimisation (before type checking)
-- Term is for run time optimisation (after type checking, collapsing allowed)

-- Compile time: no collapsing

instance Optimisable Raw where
    applyOpts t@(RApp f a)
        | (Var n, args) <- raw_unapply t -- MAGIC HERE
            = do args' <- mapM applyOpts args
                 i <- getIState
                 case lookupCtxt Nothing n (idris_optimisation i) of
                    (oi:_) -> return $ applyDataOpt oi n args'
                    _ -> return (raw_apply (Var n) args')
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


applyDataOpt :: OptInfo -> Name -> [Raw] -> Raw
applyDataOpt oi n args
    = let args' = zipWith doForce (map (\x -> x `elem` (forceable oi)) [0..]) 
                                  args in
          raw_apply (Var n) args'
  where
    doForce True  a = RForce a
    doForce False a = a

-- Run-time: do everything

instance Optimisable (TT Name) where
    applyOpts t@(App f a)
        | (c@(P (DCon t arity) n _), args) <- unApply t -- MAGIC HERE
            = do args' <- mapM applyOpts args
                 i <- getIState
                 case lookupCtxt Nothing n (idris_optimisation i) of
                      (oi:_) -> do return $ applyDataOptRT oi n t arity args'
                      _ -> return (mkApp c args')
        | otherwise = do f' <- applyOpts f
                         a' <- applyOpts a
                         return (App f' a')
    applyOpts (Bind n b t) = do b' <- applyOpts b
                                t' <- applyOpts t
                                return (Bind n b' t')
    applyOpts t = return t

-- Need to saturate arguments first to ensure that erasure happens uniformly

applyDataOptRT :: OptInfo -> Name -> Int -> Int -> [Term] -> Term
applyDataOptRT oi n tag arity args
    | length args == arity = doOpts n args (collapsible oi) (forceable oi)
    | otherwise = let extra = satArgs (arity - length args)
                      tm = doOpts n (args ++ map (\n -> P Bound n Erased) extra) 
                                    (collapsible oi) (forceable oi) in
                      bind extra tm
  where
    satArgs n = map (\i -> MN i "sat") [1..n]

    bind [] tm = tm
    bind (n:ns) tm = Bind n (Lam Erased) (pToV n (bind ns tm))

    doOpts n args True f = Erased
    doOpts n args _ forced
        = let args' = filter keep (zip (map (\x -> x `elem` forced) [0..])
                                       args) in
              mkApp (P (DCon tag (arity - length forced)) n Erased) (map snd args')

    keep (forced, _) = not forced

