{-# LANGUAGE PatternGuards #-}

module Idris.Core.Unify(match_unify, unify, Fails) where

import Idris.Core.TT
import Idris.Core.Evaluate

import Control.Monad
import Control.Monad.State.Strict
import Data.List
import Debug.Trace

-- Unification is applied inside the theorem prover. We're looking for holes
-- which can be filled in, by matching one term's normal form against another.
-- Returns a list of hole names paired with the term which solves them, and
-- a list of things which need to be injective.

-- terms which need to be injective, with the things we're trying to unify
-- at the time

type Injs = [(TT Name, TT Name, TT Name)]
type Fails = [(TT Name, TT Name, Env, Err)]

data UInfo = UI Int Fails
     deriving Show

data UResult a = UOK a
               | UPartOK a
               | UFail Err

-- Solve metavariables by matching terms against each other
-- Not really unification, of course!

match_unify :: Context -> Env -> TT Name -> TT Name -> [Name] -> [Name] ->
               TC [(Name, TT Name)]
match_unify ctxt env topx topy dont holes =
     case runStateT (un [] topx topy) (UI 0 []) of
        OK (v, UI _ []) -> return (map (renameBinders env) (trimSolutions v))
        res ->
               let topxn = normalise ctxt env topx
                   topyn = normalise ctxt env topy in
                     case runStateT (un [] topxn topyn)
        	  	        (UI 0 []) of
                       OK (v, UI _ fails) ->
                            return (map (renameBinders env) (trimSolutions v))
                       Error e ->
                        -- just normalise the term we're matching against
                         case runStateT (un [] topxn topy)
        	  	          (UI 0 []) of
                           OK (v, UI _ fails) ->
                              return (map (renameBinders env) (trimSolutions v))
                           _ -> tfail e
  where


    un names (P _ x _) tm
        | holeIn env x || x `elem` holes
            = do sc 1; checkCycle names (x, tm)
    un names tm (P _ y _)
        | holeIn env y || y `elem` holes
            = do sc 1; checkCycle names (y, tm)
    un bnames (V i) (P _ x _)
        | fst (bnames!!i) == x || snd (bnames!!i) == x = do sc 1; return []
    un bnames (P _ x _) (V i)
        | fst (bnames!!i) == x || snd (bnames!!i) == x = do sc 1; return []
    un bnames (Bind x bx sx) (Bind y by sy)
        = do h1 <- uB bnames bx by
             h2 <- un ((x, y) : bnames) sx sy
             combine bnames h1 h2
    un names (App fx ax) (App fy ay)
        = do hf <- un names fx fy
             ha <- un names ax ay
             combine names hf ha
    un names x y
        | OK True <- convEq' ctxt x y = do sc 1; return []
        | otherwise = do UI s f <- get
                         let r = recoverable x y
                         let err = CantUnify r
                                     topx topy (CantUnify r x y (Msg "") [] s) (errEnv env) s
                         if (not r) then lift $ tfail err
                           else do put (UI s ((x, y, env, err) : f))
                                   lift $ tfail err


    uB bnames (Let tx vx) (Let ty vy) = do h1 <- un bnames tx ty
                                           h2 <- un bnames vx vy
                                           combine bnames h1 h2
    uB bnames (Lam tx) (Lam ty) = un bnames tx ty
    uB bnames (Pi tx) (Pi ty) = un bnames tx ty
    uB bnames x y = do UI s f <- get
                       let r = recoverable (binderTy x) (binderTy y)
                       let err = CantUnify r topx topy
                                  (CantUnify r (binderTy x) (binderTy y) (Msg "") [] s)
                                  (errEnv env) s
                       put (UI s ((binderTy x, binderTy y, env, err) : f))
                       return []

    -- TODO: there's an annoying amount of repetition between this and the
    -- main unification function. Consider lifting it out.

    sc i = do UI s f <- get
              put (UI (s+i) f)

    unifyFail x y = do UI s f <- get
                       let r = recoverable x y
                       let err = CantUnify r
                                   topx topy (CantUnify r x y (Msg "") [] s) (errEnv env) s
                       put (UI s ((x, y, env, err) : f))
                       lift $ tfail err
    combine bnames as [] = return as
    combine bnames as ((n, t) : bs)
        = case lookup n as of
            Nothing -> combine bnames (as ++ [(n,t)]) bs
            Just t' -> do ns <- un bnames t t'
                          -- make sure there's n mapping from n in ns
                          let ns' = filter (\ (x, _) -> x/=n) ns
                          sc 1
                          combine bnames as (ns' ++ bs)

    checkCycle ns p@(x, P _ _ _) = return [p]
    checkCycle ns (x, tm)
        | not (x `elem` freeNames tm) = checkScope ns (x, tm)
        | otherwise = lift $ tfail (InfiniteUnify x tm (errEnv env))

    checkScope ns (x, tm) =
          case boundVs (envPos x 0 env) tm of
               [] -> return [(x, tm)]
               (i:_) -> lift $ tfail (UnifyScope x (fst (ns!!i))
                                     (inst ns tm) (errEnv env))
      where inst [] tm = tm
            inst ((n, _) : ns) tm = inst ns (substV (P Bound n Erased) tm)
    
renameBinders :: Env -> (Name, TT Name) -> (Name, TT Name)
renameBinders env (x, tm) = (x, uniqueBinders tm)
  where
    uniqueBinders (Bind n b sc)
        | n `elem` map fst env 
             = let n' = uniqueName n (map fst env) in
                   Bind n' (fmap uniqueBinders b)
                           (uniqueBinders (rename n n' sc))
        | otherwise = Bind n (fmap uniqueBinders b) (uniqueBinders sc)
    uniqueBinders (App f a) = App (uniqueBinders f) (uniqueBinders a)
    uniqueBinders t = t

    rename n n' (P nt x ty) | n == x = P nt n' ty
    rename n n' (Bind x b sc) = Bind x (fmap (rename n n') b) (rename n n' sc)
    rename n n' (App f a) = App (rename n n' f) (rename n n' a)
    rename n n' t = t

trimSolutions ns = dropPairs ns
  where dropPairs [] = []
        dropPairs (n@(x, P _ x' _) : ns)
          | x == x' = dropPairs ns
          | otherwise
            = n : dropPairs 
                    (filter (\t -> case t of
                                      (n, P _ n' _) -> not (n == x' && n' == x)
                                      _ -> True) ns)
        dropPairs (n : ns) = n : dropPairs ns
            
expandLets env (x, tm) = (x, doSubst (reverse env) tm)
  where
    doSubst [] tm = tm
    doSubst ((n, Let v t) : env) tm
        = doSubst env (subst n v tm)
    doSubst (_ : env) tm
        = doSubst env tm


unify :: Context -> Env -> TT Name -> TT Name -> [Name] -> [Name] ->
         TC ([(Name, TT Name)], Fails)
unify ctxt env topx topy dont holes =
--      trace ("Unifying " ++ show (topx, topy)) $
             -- don't bother if topx and topy are different at the head
      case runStateT (un False [] topx topy) (UI 0 []) of
        OK (v, UI _ []) -> return (map (renameBinders env) (trimSolutions v),
                                   [])
        res ->
               let topxn = normalise ctxt env topx
                   topyn = normalise ctxt env topy in
--                     trace ("Unifying " ++ show (topx, topy) ++ "\n\n==>\n" ++ show (topxn, topyn) ++ "\n\n" ++ show res ++ "\n\n") $
                     case runStateT (un False [] topxn topyn)
        	  	        (UI 0 []) of
                       OK (v, UI _ fails) ->
                            return (map (renameBinders env) (trimSolutions v), 
                                    reverse fails)
--         Error e@(CantUnify False _ _ _ _ _)  -> tfail e
        	       Error e -> tfail e
  where
    headDiff (P (DCon _ _) x _) (P (DCon _ _) y _) = x /= y
    headDiff (P (TCon _ _) x _) (P (TCon _ _) y _) = x /= y
    headDiff _ _ = False

    injective (P (DCon _ _) _ _) = True
    injective (P (TCon _ _) _ _) = True
--     injective (App f (P _ _ _))  = injective f
--     injective (App f (Constant _))  = injective f
    injective (App f a)          = injective f -- && injective a
    injective _                  = False

    notP (P _ _ _) = False
    notP _ = True

    sc i = do UI s f <- get
              put (UI (s+i) f)

    errors = do UI s f <- get
                return (not (null f))

    uplus u1 u2 = do UI s f <- get
                     r <- u1
                     UI s f' <- get
                     if (length f == length f')
                        then return r
                        else do put (UI s f); u2

    un :: Bool -> [(Name, Name)] -> TT Name -> TT Name ->
          StateT UInfo
          TC [(Name, TT Name)]
    un = un'
--     un fn names x y
--         = let (xf, _) = unApply x
--               (yf, _) = unApply y in
--               if headDiff xf yf then unifyFail x y else
--                   uplus (un' fn names x y)
--                         (un' fn names (hnf ctxt env x) (hnf ctxt env y))

    un' :: Bool -> [(Name, Name)] -> TT Name -> TT Name ->
           StateT UInfo
           TC [(Name, TT Name)]
    un' fn names x y | x == y = return [] -- shortcut
    un' fn names topx@(P (DCon _ _) x _) topy@(P (DCon _ _) y _)
                | x /= y = unifyFail topx topy
    un' fn names topx@(P (TCon _ _) x _) topy@(P (TCon _ _) y _)
                | x /= y = unifyFail topx topy
    un' fn names topx@(P (DCon _ _) x _) topy@(P (TCon _ _) y _)
                = unifyFail topx topy
    un' fn names topx@(P (TCon _ _) x _) topy@(P (DCon _ _) y _)
                = unifyFail topx topy
    un' fn names topx@(Constant _) topy@(P (TCon _ _) y _)
                = unifyFail topx topy
    un' fn names topx@(P (TCon _ _) x _) topy@(Constant _)
                = unifyFail topx topy
    un' fn bnames tx@(P _ x _) ty@(P _ y _)
        | (x,y) `elem` bnames || x == y = do sc 1; return []
        | injective tx && not (holeIn env y || y `elem` holes)
             = unifyTmpFail tx ty
        | injective ty && not (holeIn env x || x `elem` holes)
             = unifyTmpFail tx ty
    un' fn bnames xtm@(P _ x _) tm
        | holeIn env x || x `elem` holes
                       = do UI s f <- get
                            -- injectivity check
                            if (notP tm && fn)
--                               trace (show (x, tm, normalise ctxt env tm)) $
--                                 put (UI s ((tm, topx, topy) : i) f)
                                 then unifyTmpFail xtm tm
                                 else do sc 1
                                         checkCycle bnames (x, tm)
        | not (injective xtm) && injective tm = unifyFail xtm tm
    un' fn bnames tm ytm@(P _ y _)
        | holeIn env y || y `elem` holes
                       = do UI s f <- get
                            -- injectivity check
                            if (notP tm && fn)
--                               trace (show (y, tm, normalise ctxt env tm)) $
--                                 put (UI s ((tm, topx, topy) : i) f)
                                 then unifyTmpFail tm ytm
                                 else do sc 1
                                         checkCycle bnames (y, tm)
        | not (injective ytm) && injective tm = unifyFail ytm tm
    un' fn bnames (V i) (P _ x _)
        | fst (bnames!!i) == x || snd (bnames!!i) == x = do sc 1; return []
    un' fn bnames (P _ x _) (V i)
        | fst (bnames!!i) == x || snd (bnames!!i) == x = do sc 1; return []

    un' fn bnames appx@(App _ _) appy@(App _ _)
        = unApp fn bnames appx appy
--         = uplus (unApp fn bnames appx appy)
--                 (unifyTmpFail appx appy) -- take the whole lot

    un' fn bnames x (Bind n (Lam t) (App y (P Bound n' _)))
        | n == n' = un' False bnames x y
    un' fn bnames (Bind n (Lam t) (App x (P Bound n' _))) y
        | n == n' = un' False bnames x y
    un' fn bnames x (Bind n (Lam t) (App y (V 0)))
        = un' False bnames x y
    un' fn bnames (Bind n (Lam t) (App x (V 0))) y
        = un' False bnames x y
--     un' fn bnames (Bind x (PVar _) sx) (Bind y (PVar _) sy)
--         = un' False ((x,y):bnames) sx sy
--     un' fn bnames (Bind x (PVTy _) sx) (Bind y (PVTy _) sy)
--         = un' False ((x,y):bnames) sx sy

    -- f D unifies with t -> D. This is dubious, but it helps with type
    -- class resolution for type classes over functions.

    un' fn bnames (App f x) (Bind n (Pi t) y)
      | noOccurrence n y && x == y
        = un' False bnames f (Bind (sMN 0 "uv") (Lam (TType (UVar 0))) 
                                   (Bind n (Pi t) (V 1)))
             
    un' fn bnames (Bind x bx sx) (Bind y by sy)
        = do h1 <- uB bnames bx by
             h2 <- un' False ((x,y):bnames) sx sy
             combine bnames h1 h2
    un' fn bnames x y
        | OK True <- convEq' ctxt x y = do sc 1; return []
        | otherwise = do UI s f <- get
                         let r = recoverable x y
                         let err = CantUnify r
                                     topx topy (CantUnify r x y (Msg "") [] s) (errEnv env) s
                         if (not r) then lift $ tfail err
                           else do put (UI s ((x, y, env, err) : f))
                                   return [] -- lift $ tfail err

    unApp fn bnames appx@(App fx ax) appy@(App fy ay)
         | (injective fx && injective fy)
        || (injective fx && rigid appx && metavarApp appy)
        || (injective fy && rigid appy && metavarApp appx)
        || (injective fx && metavarApp fy && ax == ay)
        || (injective fy && metavarApp fx && ax == ay)
         = do let (headx, _) = unApply fx
              let (heady, _) = unApply fy
              -- fail quickly if the heads are disjoint
              checkHeads headx heady
--              if True then -- (injective fx || injective fy || fx == fy) then
--              if (injective fx && metavarApp appy) ||
--                 (injective fy && metavarApp appx) ||
--                 (injective fx && injective fy) || fx == fy
              uplus
                (do hf <- un' True bnames fx fy
                    let ax' = hnormalise hf ctxt env (substNames hf ax)
                    let ay' = hnormalise hf ctxt env (substNames hf ay)
                    ha <- un' False bnames ax' ay'
                    sc 1
                    combine bnames hf ha)
                (do ha <- un' False bnames ax ay
                    let fx' = hnormalise ha ctxt env (substNames ha fx)
                    let fy' = hnormalise ha ctxt env (substNames ha fy)
                    hf <- un' False bnames fx' fy'
                    sc 1
                    combine bnames hf ha)
       | otherwise = -- trace (show (appx, appy, injective fx, metavarApp appy, sameArgStruct appx appy)) $
            do let (headx, argsx) = unApply appx
               let (heady, argsy) = unApply appy
               -- traceWhen (headx == heady) (show (appx, appy)) $
               uplus (
                 if (length argsx == length argsy &&
                    ((headx == heady && inenv headx) || (argsx == argsy) ||
                     (and (zipWith sameStruct (headx:argsx) (heady:argsy)))))
                       then
--                      (notFn headx && notFn heady))) then
                   do uf <- un' True bnames headx heady
                      failed <- errors
                      if (not failed) then unArgs uf argsx argsy
                        else return []
                   else -- trace ("TMPFAIL " ++ show (appx, appy, injective appx, injective appy)) $
                        unifyTmpFail appx appy)
                    (unifyTmpFail appx appy) -- whole application fails
      where hnormalise [] _ _ t = t
            hnormalise ns ctxt env t = normalise ctxt env t
            checkHeads (P (DCon _ _) x _) (P (DCon _ _) y _)
                | x /= y = unifyFail appx appy
            checkHeads (P (TCon _ _) x _) (P (TCon _ _) y _)
                | x /= y = unifyFail appx appy
            checkHeads (P (DCon _ _) x _) (P (TCon _ _) y _)
                = unifyFail appx appy
            checkHeads (P (TCon _ _) x _) (P (DCon _ _) y _)
                = unifyFail appx appy
            checkHeads _ _ = return []

            unArgs as [] [] = return as
            unArgs as (x : xs) (y : ys)
                = do let x' = hnormalise as ctxt env (substNames as x)
                     let y' = hnormalise as ctxt env (substNames as y)
                     as' <- un' False bnames x' y'
                     vs <- combine bnames as as'
                     unArgs vs xs ys

            metavarApp tm = let (f, args) = unApply tm in
                                metavar f &&
                                all (\x -> metavarApp x) args
                                   && nub args == args
            metavarArgs tm = let (f, args) = unApply tm in
                                 all (\x -> metavar x || inenv x) args
                                   && nub args == args
            metavarApp' tm = let (f, args) = unApply tm in
                                 all (\x -> pat x || metavar x) (f : args)
                                   && nub args == args

            sameArgStruct appx appy
                = let (_, ax) = unApply appx
                      (_, ay) = unApply appy in
                      length ax == length ay &&
                        and (zipWith sameStruct ax ay)

            sameStruct fapp@(App f x) gapp@(App g y)
                = let (f',a') = unApply fapp
                      (g',b') = unApply gapp in
                      (f' == g' && length a' == length b' &&
                          (injective f' || injective g'))
                        || (sameStruct f g && sameStruct x y)
            sameStruct (P _ x _) (P _ y _) = True
            sameStruct (V i) (V j) = i == j
            sameStruct (Constant x) (Constant y) = True
            sameStruct (P _ _ _) (Constant y) = True
            sameStruct (Constant x) (P _ _ _) = True
            sameStruct (Bind n t sc) (P _ _ _) = True
            sameStruct (P _ _ _) (Bind n t sc) = True
            sameStruct (Bind n t sc) (Bind n' t' sc') = sameStruct sc sc'
            sameStruct _ _ = False

            rigid (P (DCon _ _) _ _) = True
            rigid (P (TCon _ _) _ _) = True
            rigid t@(P Ref _ _)      = inenv t
            rigid (Constant _)       = True
            rigid (App f a)          = rigid f && rigid a
            rigid t                  = not (metavar t)

            metavar t = case t of
                             P _ x _ -> (x `elem` holes || holeIn env x) &&
                                        not (x `elem` dont)
                             _ -> False
            pat t = case t of
                         P _ x _ -> x `elem` holes || patIn env x
                         _ -> False
            inenv t = case t of
                           P _ x _ -> x `elem` (map fst env)
                           _ -> False

            notFn t = injective t || metavar t || inenv t


    unifyTmpFail x y
                  = do UI s f <- get
                       let r = recoverable x y
                       let err = CantUnify r
                                   topx topy (CantUnify r x y (Msg "") [] s) (errEnv env) s
                       put (UI s ((topx, topy, env, err) : f))
                       return []

    -- shortcut failure, if we *know* nothing can fix it
    unifyFail x y = do UI s f <- get
                       let r = recoverable x y
                       let err = CantUnify r
                                   topx topy (CantUnify r x y (Msg "") [] s) (errEnv env) s
                       put (UI s ((topx, topy, env, err) : f))
                       lift $ tfail err


    uB bnames (Let tx vx) (Let ty vy)
        = do h1 <- un' False bnames tx ty
             h2 <- un' False bnames vx vy
             sc 1
             combine bnames h1 h2
    uB bnames (Guess tx vx) (Guess ty vy)
        = do h1 <- un' False bnames tx ty
             h2 <- un' False bnames vx vy
             sc 1
             combine bnames h1 h2
    uB bnames (Lam tx) (Lam ty) = do sc 1; un' False bnames tx ty
    uB bnames (Pi tx) (Pi ty) = do sc 1; un' False bnames tx ty
    uB bnames (Hole tx) (Hole ty) = un' False bnames tx ty
    uB bnames (PVar tx) (PVar ty) = un' False bnames tx ty
    uB bnames x y = do UI s f <- get
                       let r = recoverable (binderTy x) (binderTy y)
                       let err = CantUnify r topx topy
                                  (CantUnify r (binderTy x) (binderTy y) (Msg "") [] s)
                                  (errEnv env) s
                       put (UI s ((binderTy x, binderTy y, env, err) : f))
                       return [] -- lift $ tfail err

    checkCycle ns p@(x, P _ _ _) = return [p]
    checkCycle ns (x, tm)
        | not (x `elem` freeNames tm) = checkScope ns (x, tm)
        | otherwise = lift $ tfail (InfiniteUnify x tm (errEnv env))

    checkScope ns (x, tm) =
          case boundVs (envPos x 0 env) tm of
               [] -> return [(x, tm)]
               (i:_) -> lift $ tfail (UnifyScope x (fst (ns!!i))
                                     (inst ns tm) (errEnv env))
      where inst [] tm = tm
            inst ((n, _) : ns) tm = inst ns (substV (P Bound n Erased) tm)

    combineArgs bnames args = ca [] args where
       ca acc [] = return acc
       ca acc (x : xs) = do x' <- combine bnames acc x
                            ca x' xs

    combine bnames as [] = return as
    combine bnames as ((n, t) : bs)
        = case lookup n as of
            Nothing -> combine bnames (as ++ [(n,t)]) bs
            Just t' -> do ns <- un' False bnames t t'
                          -- make sure there's n mapping from n in ns
                          let ns' = filter (\ (x, _) -> x/=n) ns
                          sc 1
                          combine bnames as (ns' ++ bs)

boundVs :: Int -> Term -> [Int]
boundVs i (V j) | j <= i = []
                | otherwise = [j]
boundVs i (Bind n b sc) = boundVs (i + 1) sc
boundVs i (App f x) = let fs = boundVs i f
                          xs = boundVs i x in
                          nub (fs ++ xs)
boundVs i _ = []

envPos x i [] = 0
envPos x i ((y, _) : ys) | x == y = i
                         | otherwise = envPos x (i + 1) ys


-- If there are any clashes of constructors, deem it unrecoverable, otherwise some
-- more work may help.
-- FIXME: Depending on how overloading gets used, this may cause problems. Better
-- rethink overloading properly...

recoverable (P (DCon _ _) x _) (P (DCon _ _) y _)
    | x == y = True
    | otherwise = False
recoverable (P (TCon _ _) x _) (P (TCon _ _) y _)
    | x == y = True
    | otherwise = False
recoverable (Constant _) (P (DCon _ _) y _) = False
recoverable (P (DCon _ _) x _) (Constant _) = False
recoverable (Constant _) (P (TCon _ _) y _) = False
recoverable (P (TCon _ _) x _) (Constant _) = False
recoverable (P (DCon _ _) x _) (P (TCon _ _) y _) = False
recoverable (P (TCon _ _) x _) (P (DCon _ _) y _) = False
recoverable p@(Constant _) (App f a) = recoverable p f
recoverable (App f a) p@(Constant _) = recoverable f p
recoverable p@(P _ n _) (App f a) = recoverable p f
--     recoverable (App f a) p@(P _ _ _) = recoverable f p
recoverable (App f a) (App f' a')
    = recoverable f f' -- && recoverable a a'
recoverable f (Bind _ (Pi _) sc)
    | (P (DCon _ _) _ _, _) <- unApply f = False
    | (P (TCon _ _) _ _, _) <- unApply f = False
recoverable (Bind _ (Pi _) sc) f
    | (P (DCon _ _) _ _, _) <- unApply f = False
    | (P (TCon _ _) _ _, _) <- unApply f = False
recoverable _ _ = True

errEnv = map (\(x, b) -> (x, binderTy b))

holeIn :: Env -> Name -> Bool
holeIn env n = case lookup n env of
                    Just (Hole _) -> True
                    Just (Guess _ _) -> True
                    _ -> False

patIn :: Env -> Name -> Bool
patIn env n = case lookup n env of
                    Just (PVar _) -> True
                    Just (PVTy _) -> True
                    _ -> False

