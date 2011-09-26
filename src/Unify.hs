{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies, DeriveFunctor #-}

module Unify(unify) where

import Core
import Evaluate

-- Unification is applied inside the theorem prover. We're looking for holes
-- which can be filled in, by matching one term's normal form against another.
-- Returns a list of hole names paired with the term which solves them.

unify :: Context -> Env -> TT Name -> TT Name -> TC [(Name, TT Name)]
unify ctxt env x y 
    = case un' [] x y of
        OK v -> return v
        _ -> fail $ "Can't unify " ++ showEnv env x ++ " and " ++ showEnv env y
  where
    un' bnames (P Bound x _) (P Bound y _) | (x,y) `elem` bnames = return []
    un' bnames x y | x == y = return []
                   | otherwise = fail "Can't unify"

holeIn :: Env -> Name -> Bool
holeIn env n = case lookup n env of
                    Just (Hole _) -> True
                    _ -> False

