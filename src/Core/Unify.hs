{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies, DeriveFunctor #-}

module Core.Unify(unify) where

import Core.TT
import Core.Evaluate

import Control.Monad

-- Unification is applied inside the theorem prover. We're looking for holes
-- which can be filled in, by matching one term's normal form against another.
-- Returns a list of hole names paired with the term which solves them.

unify :: Context -> Env -> TT Name -> TT Name -> TC [(Name, TT Name)]
unify ctxt env x y 
    = case un' [] x y of -- try without normalising first, for speed
        OK v -> return v
        _    -> case un' [] (normalise ctxt env x) (normalise ctxt env y) of
                OK v -> return v
                _    -> fail $ "Can't unify " ++ showEnv env x ++ " and " ++ showEnv env y
  where
    un' bnames (P Bound x _)  (P Bound y _)  
        | (x,y) `elem` bnames = return []
    un' bnames (P Bound x _) tm
        | holeIn env x = return [(x, tm)]
    un' bnames tm (P Bound y _)
        | holeIn env y = return [(y, tm)]

    un' bnames x@(App _ _)    y@(App _ _)    
        = uApp bnames (unApply x) (unApply y)
    un' bnames x (Bind n (Lam t) (App y (P Bound n' _)))
        | n == n' = un' bnames x y
    un' bnames (Bind n (Lam t) (App x (P Bound n' _))) y
        | n == n' = un' bnames x y
    un' bnames (Bind x bx sx) (Bind y by sy) 
        = do h1 <- uB bnames bx by
             h2 <- un' ((x,y):bnames) sx sy
             combine bnames h1 h2
    un' bnames x y | x == y = return []
                   | otherwise = fail "Can't unify" 

    uB bnames (Let tx vx) (Let ty vy)
        = do h1 <- un' bnames tx ty
             h2 <- un' bnames ty vy
             combine bnames h1 h2
    uB bnames (Guess tx vx) (Guess ty vy)
        = do h1 <- un' bnames tx ty
             h2 <- un' bnames ty vy
             combine bnames h1 h2
    uB bnames (Lam tx) (Lam ty) = un' bnames tx ty
    uB bnames (Pi tx) (Pi ty) = un' bnames tx ty
    uB bnames (Hole tx) (Hole ty) = un' bnames tx ty
    uB bnames (PVar tx) (PVar ty) = un' bnames tx ty
    uB bnames _ _ = fail "Can't unify"

    uApp bnames (xp@(P xnt x xty), xargs) (yp@(P ynt y yty), yargs)
        | (x == y && all okToUnify [xnt, ynt]) ||
          (holeIn env x && okToUnify ynt) ||
          (okToUnify xnt && holeIn env y)
            = do h <- un' bnames xp yp
                 hargs <- zipWithM (un' bnames) xargs yargs
                 h' <- foldM (combine bnames) [] hargs
                 combine bnames h h'
    uApp bnames (xf, xargs) (yf, yargs) 
            = do un' bnames xf yf -- ignore result
                 hargs <- zipWithM (un' bnames) xargs yargs
                 foldM (combine bnames) [] hargs 

    okToUnify (DCon _ _) = True
    okToUnify (TCon _) = True
    okToUnify _ = False

    combine bnames as [] = return as
    combine bnames as ((n, t) : bs)
        = case lookup n as of 
            Nothing -> combine bnames (as ++ [(n,t)]) bs
            Just t' -> do un' bnames t t'
                          combine bnames as bs

holeIn :: Env -> Name -> Bool
holeIn env n = case lookup n env of
                    Just (Hole _) -> True
                    _ -> False

