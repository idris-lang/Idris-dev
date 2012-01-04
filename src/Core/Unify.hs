module Core.Unify(unify) where

import Core.TT
import Core.Evaluate

import Control.Monad
import Control.Monad.State
import Debug.Trace

-- Unification is applied inside the theorem prover. We're looking for holes
-- which can be filled in, by matching one term's normal form against another.
-- Returns a list of hole names paired with the term which solves them, and
-- a list of things which need to be injective.

-- terms which need to be injective, with the things we're trying to unify
-- at the time
type UInfo = [(TT Name, TT Name, TT Name)] 

unify :: Context -> Env -> TT Name -> TT Name -> TC ([(Name, TT Name)], 
                                                     UInfo)
unify ctxt env topx topy 
    = case runStateT 
             (un' False [] (normalise ctxt env topx) (normalise ctxt env topy))
             [] of
              OK (v, inj) -> return (filter notTrivial v, inj)
              Error e -> tfail $ CantUnify topx topy e  
  where
    notTrivial (x, P _ x' _) = x /= x'
    notTrivial _ = True

    injective (P (DCon _ _) _ _) = True
    injective (P (TCon _ _) _ _) = True
    injective (App f a)          = injective f
    injective _                  = False

    notP (P _ _ _) = False
    notP _ = True

    un' :: Bool -> [(Name, Name)] -> TT Name -> TT Name ->
           StateT UInfo 
           TC [(Name, TT Name)]
    un' fn bnames (P Bound x _)  (P Bound y _)  
        | (x,y) `elem` bnames = return []
    un' fn bnames (P Bound x _) tm
        | holeIn env x = do i <- get
                            when (notP tm && fn) $ put ((tm, topx, topy) : i)
                            return [(x, tm)]
    un' fn bnames tm (P Bound y _)
        | holeIn env y = do i <- get
                            when (notP tm && fn) $ put ((tm, topx, topy) : i)
                            return [(y, tm)]
    un' fn bnames (V i) (P Bound x _)
        | fst (bnames!!i) == x || snd (bnames!!i) == x = return []
    un' fn bnames (P Bound x _) (V i)
        | fst (bnames!!i) == x || snd (bnames!!i) == x = return []

    un' fn bnames (App fx ax) (App fy ay)    
        = do hf <- un' True bnames fx fy 
             let ax' = normalise ctxt env (substNames hf ax)
             let ay' = normalise ctxt env (substNames hf ay)
             ha <- un' False bnames ax' ay'
             combine bnames hf ha

    un' fn bnames x (Bind n (Lam t) (App y (P Bound n' _)))
        | n == n' = un' False bnames x y
    un' fn bnames (Bind n (Lam t) (App x (P Bound n' _))) y
        | n == n' = un' False bnames x y
    un' fn bnames (Bind x bx sx) (Bind y by sy) 
        = do h1 <- uB bnames bx by
             h2 <- un' False ((x,y):bnames) sx sy
             combine bnames h1 h2
    un' fn bnames x y 
        | x == y = return []
        | otherwise = fail $ "Can't unify " ++ show x ++ " and " ++ show y
                             ++ " " ++ show bnames ++ " " ++ show env

    uB bnames (Let tx vx) (Let ty vy)
        = do h1 <- un' False bnames tx ty
             h2 <- un' False bnames ty vy
             combine bnames h1 h2
    uB bnames (Guess tx vx) (Guess ty vy)
        = do h1 <- un' False bnames tx ty
             h2 <- un' False bnames ty vy
             combine bnames h1 h2
    uB bnames (Lam tx) (Lam ty) = un' False bnames tx ty
    uB bnames (Pi tx) (Pi ty) = un' False bnames tx ty
    uB bnames (Hole tx) (Hole ty) = un' False bnames tx ty
    uB bnames (PVar tx) (PVar ty) = un' False bnames tx ty
    uB bnames _ _ = fail "Can't unify"

    combine bnames as [] = return as
    combine bnames as ((n, t) : bs)
        = case lookup n as of 
            Nothing -> combine bnames (as ++ [(n,t)]) bs
            Just t' -> do un' False bnames t t'
                          combine bnames as bs

holeIn :: Env -> Name -> Bool
holeIn env n = case lookup n env of
                    Just (Hole _) -> True
                    _ -> False

