module Core.Unify(unify) where

import Core.TT
import Core.Evaluate

import Control.Monad
import Debug.Trace

-- Unification is applied inside the theorem prover. We're looking for holes
-- which can be filled in, by matching one term's normal form against another.
-- Returns a list of hole names paired with the term which solves them.

-- FIXME! Needs to be cleverer: when we solve a variable, fill it in and normalise
-- to help the rest of the unification

unify :: Context -> Env -> TT Name -> TT Name -> TC [(Name, TT Name)]
unify ctxt env topx topy 
    = case un' [] (normalise ctxt env topx) (normalise ctxt env topy) of
              OK v -> return v
              Error e -> tfail $ CantUnify topx topy e  
  where
    un' bnames (P Bound x _)  (P Bound y _)  
        | (x,y) `elem` bnames = return []
    un' bnames (P Bound x _) tm
        | holeIn env x = return [(x, tm)]
    un' bnames tm (P Bound y _)
        | holeIn env y = return [(y, tm)]
    un' bnames (V i) (P Bound x _)
        | fst (bnames!!i) == x || snd (bnames!!i) == x = return []
    un' bnames (P Bound x _) (V i)
        | fst (bnames!!i) == x || snd (bnames!!i) == x = return []

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
                   | otherwise = fail $ "Can't unify " ++ show x ++ " and " ++ show y
                                        ++ " " ++ show bnames ++ " " ++ show env

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
        | (x == y && all okToUnify [xnt, ynt]) || -- functions x,y are injectice
          (holeIn env x && okToUnify ynt) ||
          (okToUnify xnt && holeIn env y)
            = do h <- un' bnames xp yp
                 uArgs bnames h xargs yargs
        | x == y && xargs == yargs -- only ok if arguments are equal, if functions
                                   -- are not known to be injetive
            = return []
    uApp bnames (xf, xargs) (yf, yargs) 
            = do un' bnames xf yf -- ignore result
                 uArgs bnames [] xargs yargs

    okToUnify (DCon _ _) = True
    okToUnify (TCon _) = True
    okToUnify _ = False

    uArgs bnames h [] [] = return h
    uArgs bnames h (x:xs) (y:ys) = 
        case un' bnames x y of
           OK h' -> do next <- combine bnames h h' 
                       uArgs bnames next xs ys
           _ -> do let x' = normalise ctxt env (substNames h x)
                   let y' = normalise ctxt env (substNames h y)
                   h' <- un' bnames x' y'
                   next <- combine bnames h h'
                   uArgs bnames next xs ys
    uArgs bnames h _ _ = fail "Can't unify; argument lists different length"

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

