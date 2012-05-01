{-# LANGUAGE PatternGuards #-}

module Core.Unify(unify, Fails) where

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

type Injs = [(TT Name, TT Name, TT Name)]
type Fails = [(TT Name, TT Name, Env, Err)]

data UInfo = UI Int Injs Fails

unify :: Context -> Env -> TT Name -> TT Name -> TC ([(Name, TT Name)], 
                                                     Injs, Fails)
unify ctxt env topx topy 
    = case runStateT 
             (un' False [] (normalise ctxt env topx) (normalise ctxt env topy))
             (UI 0 [] []) of
              OK (v, UI _ inj fails) -> return (filter notTrivial v, inj, reverse fails)
--               OK (_, UI s _ ((_,_,f):fs)) -> tfail $ CantUnify topx topy f s
              Error e -> tfail e
  where
    notTrivial (x, P _ x' _) = x /= x'
    notTrivial _ = True

    injective (P (DCon _ _) _ _) = True
    injective (P (TCon _ _) _ _) = True
    injective (App f a)          = injective f
    injective _                  = False

    notP (P _ _ _) = False
    notP _ = True

    sc i = do UI s x f <- get
              put (UI (s+i) x f)

    uplus u1 u2 = do UI s i f <- get
                     r <- u1
                     UI s _ f' <- get
                     if (length f == length f') 
                        then return r
                        else do put (UI s i f); u2

    un' :: Bool -> [(Name, Name)] -> TT Name -> TT Name ->
           StateT UInfo 
           TC [(Name, TT Name)]
    un' fn bnames (P Bound x _)  (P Bound y _)  
        | (x,y) `elem` bnames = do sc 1; return []
    un' fn bnames (P Bound x _) tm
        | holeIn env x = do UI s i f <- get
                            when (notP tm && fn) $ put (UI s ((tm, topx, topy) : i) f)
                            sc 1
                            return [(x, tm)]
    un' fn bnames tm (P Bound y _)
        | holeIn env y = do UI s i f <- get
                            when (notP tm && fn) $ put (UI s ((tm, topx, topy) : i) f)
                            sc 1
                            return [(y, tm)]
    un' fn bnames (V i) (P Bound x _)
        | fst (bnames!!i) == x || snd (bnames!!i) == x = do sc 1; return []
    un' fn bnames (P Bound x _) (V i)
        | fst (bnames!!i) == x || snd (bnames!!i) == x = do sc 1; return []

    un' fn bnames (App fx ax) (App fy ay)    
        = do uplus -- do the second one if the first adds any errors 
                (do hf <- un' True bnames fx fy 
                    let ax' = normalise ctxt env (substNames hf ax)
                    let ay' = normalise ctxt env (substNames hf ay)
                    ha <- un' False bnames ax' ay'
                    sc 1
                    combine bnames hf ha)
                (do ha <- un' False bnames ax ay
                    let fx' = normalise ctxt env (substNames ha fx)
                    let fy' = normalise ctxt env (substNames ha fy)
                    hf <- un' False bnames fx' fy'
                    sc 1
                    combine bnames hf ha)

    un' fn bnames x (Bind n (Lam t) (App y (P Bound n' _)))
        | n == n' = un' False bnames x y
    un' fn bnames (Bind n (Lam t) (App x (P Bound n' _))) y
        | n == n' = un' False bnames x y
    un' fn bnames (Bind x bx sx) (Bind y by sy) 
        = do h1 <- uB bnames bx by
             h2 <- un' False ((x,y):bnames) sx sy
             combine bnames h1 h2
    un' fn bnames x y 
        | OK True <- convEq' ctxt x y = do sc 1; return []
        | otherwise = do UI s i f <- get
                         let err = CantUnify topx topy (CantUnify x y (Msg "") [] s) (errEnv env) s
                         put (UI s i ((x, y, env, err) : f))
                         return [] -- lift $ tfail err

    uB bnames (Let tx vx) (Let ty vy)
        = do h1 <- un' False bnames tx ty
             h2 <- un' False bnames ty vy
             sc 1
             combine bnames h1 h2
    uB bnames (Guess tx vx) (Guess ty vy)
        = do h1 <- un' False bnames tx ty
             h2 <- un' False bnames ty vy
             sc 1
             combine bnames h1 h2
    uB bnames (Lam tx) (Lam ty) = do sc 1; un' False bnames tx ty
    uB bnames (Pi tx) (Pi ty) = do sc 1; un' False bnames tx ty
    uB bnames (Hole tx) (Hole ty) = un' False bnames tx ty
    uB bnames (PVar tx) (PVar ty) = un' False bnames tx ty
    uB bnames x y = do UI s i f <- get
                       let err = CantUnify topx topy
                                  (CantUnify (binderTy x) (binderTy y) (Msg "") [] s)
                                  (errEnv env) s
                       put (UI s i ((binderTy x, binderTy y, env, err) : f))
                       return [] -- lift $ tfail err

    combine bnames as [] = return as
    combine bnames as ((n, t) : bs)
        = case lookup n as of 
            Nothing -> combine bnames (as ++ [(n,t)]) bs
            Just t' -> do un' False bnames t t'
                          sc 1
                          combine bnames as bs

errEnv = map (\(x, b) -> (x, binderTy b))

holeIn :: Env -> Name -> Bool
holeIn env n = case lookup n env of
                    Just (Hole _) -> True
                    _ -> False

