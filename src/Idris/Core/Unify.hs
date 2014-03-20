{-# LANGUAGE PatternGuards #-}

module Idris.Core.Unify(match_unify, unify, Fails, FailContext(..), FailAt(..)) where

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

data FailAt = Match | Unify
     deriving (Show, Eq)

data FailContext = FailContext { fail_sourceloc :: FC,
                                 fail_fn        :: Name,
                                 fail_param     :: Name
                               }
  deriving (Eq, Show)

type Injs = [(TT Name, TT Name, TT Name)]
type Fails = [(TT Name, TT Name, Env, Err, [FailContext], FailAt)]

data UInfo = UI Int Fails
     deriving Show

data UResult a = UOK a
               | UPartOK a
               | UFail Err

-- | Smart constructor for unification errors that takes into account the FailContext
cantUnify :: [FailContext] -> Bool -> t -> t -> (Err' t) -> [(Name, t)] -> Int -> Err' t
cantUnify [] r t1 t2 e ctxt i = CantUnify r t1 t2 e ctxt i
cantUnify (FailContext fc f x : _) r t1 t2 e ctxt i =
  At fc (ElaboratingArg f x (CantUnify r t1 t2 e ctxt i))

-- Solve metavariables by matching terms against each other
-- Not really unification, of course!

match_unify :: Context -> Env -> TT Name -> TT Name -> [Name] -> [Name] -> [FailContext] ->
               TC [(Name, TT Name)]
match_unify ctxt env topx topy inj holes from =
     case runStateT (un [] (renameBindersTm env topx)
                           (renameBindersTm env topy)) (UI 0 []) of
        OK (v, UI _ []) -> return (map (renameBinders env) (trimSolutions v))
        res ->
               let topxn = renameBindersTm env (normalise ctxt env topx)
                   topyn = renameBindersTm env (normalise ctxt env topy) in
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
        | length bnames > i, 
          fst (fst (bnames!!i)) == x || 
          snd (fst (bnames!!i)) == x = do sc 1; return []
    un bnames (P _ x _) (V i)
        | length bnames > i,
          fst (fst (bnames!!i)) == x || 
          snd (fst (bnames!!i)) == x = do sc 1; return []
    un bnames (Bind x bx sx) (Bind y by sy)
        = do h1 <- uB bnames bx by
             h2 <- un (((x, y), binderTy bx) : bnames) sx sy
             combine bnames h1 h2
    un names (App fx ax) (App fy ay)
        = do hf <- un names fx fy
             ha <- un names ax ay
             combine names hf ha
    un names x y
        | OK True <- convEq' ctxt holes x y = do sc 1; return []
        | otherwise = do UI s f <- get
                         let r = recoverable x y
                         let err = cantUnify from r
                                     topx topy (CantUnify r x y (Msg "") (errEnv env) s) (errEnv env) s
                         if (not r) then lift $ tfail err
                           else do put (UI s ((x, y, env, err, from, Match) : f))
                                   lift $ tfail err


    uB bnames (Let tx vx) (Let ty vy) = do h1 <- un bnames tx ty
                                           h2 <- un bnames vx vy
                                           combine bnames h1 h2
    uB bnames (Lam tx) (Lam ty) = un bnames tx ty
    uB bnames (Pi tx) (Pi ty) = un bnames tx ty
    uB bnames x y = do UI s f <- get
                       let r = recoverable (binderTy x) (binderTy y)
                       let err = cantUnify from r topx topy
                                   (CantUnify r (binderTy x) (binderTy y) (Msg "") (errEnv env) s)
                                   (errEnv env) s
                       put (UI s ((binderTy x, binderTy y, env, err, from, Match) : f))
                       return []

    -- TODO: there's an annoying amount of repetition between this and the
    -- main unification function. Consider lifting it out.

    sc i = do UI s f <- get
              put (UI (s+i) f)

    unifyFail x y = do UI s f <- get
                       let r = recoverable x y
                       let err = cantUnify from r
                                   topx topy (CantUnify r x y (Msg "") (errEnv env) s) (errEnv env) s
                       put (UI s ((x, y, env, err, from, Match) : f))
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
--           case boundVs (envPos x 0 env) tm of
--                [] -> return [(x, tm)]
--                (i:_) -> lift $ tfail (UnifyScope x (fst (fst (ns!!i)))
--                                      (inst ns tm) (errEnv env))
        let v = highV (-1) tm in
            if v >= length ns
               then lift $ tfail (Msg "SCOPE ERROR")
               else return [(x, bind v ns tm)]
      where inst [] tm = tm
            inst ((n, _) : ns) tm = inst ns (substV (P Bound n Erased) tm)

    bind i ns tm 
      | i < 0 = tm
      | otherwise = let ((x,y),ty) = ns!!i in
                        App (Bind y (Lam ty) (bind (i-1) ns tm))
                            (P Bound x ty)
    
renameBinders env (x, t) = (x, renameBindersTm env t)

renameBindersTm :: Env -> TT Name -> TT Name
renameBindersTm env tm = uniqueBinders (map fst env) tm
  where
    uniqueBinders env (Bind n b sc)
        | n `elem` env 
             = let n' = uniqueName n env in
                   Bind n' (fmap (uniqueBinders env) b)
                           (uniqueBinders (n':env) (rename n n' sc))
        | otherwise = Bind n (fmap (uniqueBinders (n:env)) b) 
                             (uniqueBinders (n:env) sc)
    uniqueBinders env (App f a) = App (uniqueBinders env f) (uniqueBinders env a)
    uniqueBinders env t = t

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


unify :: Context -> Env -> TT Name -> TT Name -> [Name] -> [Name] -> [FailContext] ->
         TC ([(Name, TT Name)], Fails)
unify ctxt env topx topy inj holes from =
--      trace ("Unifying " ++ show (topx, topy)) $
             -- don't bother if topx and topy are different at the head
      case runStateT (un False [] (renameBindersTm env topx) 
                                  (renameBindersTm env topy)) (UI 0 []) of
        OK (v, UI _ []) -> return (map (renameBinders env) (trimSolutions v),
                                   [])
        res ->
               let topxn = renameBindersTm env (normalise ctxt env topx)
                   topyn = renameBindersTm env (normalise ctxt env topy) in
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

--     injectiveVar (P _ (MN _ _) _) = True -- TMP HACK 
    injectiveVar (P _ n _)        = n `elem` inj 
    injectiveVar (App f a)        = injectiveVar f -- && injective a
    injectiveVar _ = False

    injectiveApp x = injective x || injectiveVar x

    notP (P _ _ _) = False
    notP _ = True

    sc i = do UI s f <- get
              put (UI (s+i) f)

    errors :: StateT UInfo TC Bool
    errors = do UI s f <- get
                return (not (null f))

    uplus u1 u2 = do UI s f <- get
                     r <- u1
                     UI s f' <- get
                     if (length f == length f')
                        then return r
                        else do put (UI s f); u2

    un :: Bool -> [((Name, Name), TT Name)] -> TT Name -> TT Name ->
          StateT UInfo
          TC [(Name, TT Name)]
    un = un'
--     un fn names x y
--         = let (xf, _) = unApply x
--               (yf, _) = unApply y in
--               if headDiff xf yf then unifyFail x y else
--                   uplus (un' fn names x y)
--                         (un' fn names (hnf ctxt env x) (hnf ctxt env y))

    un' :: Bool -> [((Name, Name), TT Name)] -> TT Name -> TT Name ->
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
        | (x,y) `elem` map fst bnames || x == y = do sc 1; return []
        | injective tx && not (holeIn env y || y `elem` holes)
             = unifyTmpFail tx ty
        | injective ty && not (holeIn env x || x `elem` holes)
             = unifyTmpFail tx ty
    un' fn bnames xtm@(P _ x _) tm
        | holeIn env x || x `elem` holes
                       = do UI s f <- get
                            -- injectivity check
                            x <- checkCycle bnames (x, tm)
                            if (notP tm && fn)
--                               trace (show (x, tm, normalise ctxt env tm)) $
--                                 put (UI s ((tm, topx, topy) : i) f)
                                 then unifyTmpFail xtm tm
                                 else do sc 1
                                         return x
        | not (injective xtm) && injective tm 
                       = do checkCycle bnames (x, tm)
                            unifyTmpFail xtm tm
    un' fn bnames tm ytm@(P _ y _)
        | holeIn env y || y `elem` holes
                       = do UI s f <- get
                            -- injectivity check
                            x <- checkCycle bnames (y, tm)
                            if (notP tm && fn)
--                               trace (show (y, tm, normalise ctxt env tm)) $
--                                 put (UI s ((tm, topx, topy) : i) f)
                                 then unifyTmpFail tm ytm
                                 else do sc 1
                                         return x
        | not (injective ytm) && injective tm 
                       = do checkCycle bnames (y, tm)
                            unifyTmpFail tm ytm
    un' fn bnames (V i) (P _ x _)
        | length bnames > i,
          fst ((map fst bnames)!!i) == x || 
          snd ((map fst bnames)!!i) == x = do sc 1; return []
    un' fn bnames (P _ x _) (V i)
        | length bnames > i,
          fst ((map fst bnames)!!i) == x || 
          snd ((map fst bnames)!!i) == x = do sc 1; return []

    un' fn names topx@(Bind n (Hole t) sc) y = unifyTmpFail topx y
    un' fn names x topy@(Bind n (Hole t) sc) = unifyTmpFail x topy

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
      | noOccurrence n y && injectiveApp f
        = do ux <- un' False bnames x y
             uf <- un' False bnames f (Bind (sMN 0 "uv") (Lam (TType (UVar 0))) 
                                      (Bind n (Pi t) (V 1)))
             combine bnames ux uf
             
    un' fn bnames (Bind n (Pi t) y) (App f x)
      | noOccurrence n y && injectiveApp f
        = do ux <- un' False bnames y x
             uf <- un' False bnames (Bind (sMN 0 "uv") (Lam (TType (UVar 0))) 
                                    (Bind n (Pi t) (V 1))) f
             combine bnames ux uf
             
    un' fn bnames (Bind x bx sx) (Bind y by sy)
        | sameBinder bx by
           = do h1 <- uB bnames bx by
                h2 <- un' False (((x,y),binderTy bx):bnames) sx sy
                combine bnames h1 h2
      where sameBinder (Lam _) (Lam _) = True
            sameBinder (Pi _) (Pi _) = True
            sameBinder _ _ = False
    un' fn bnames x y
        | OK True <- convEq' ctxt holes x y = do sc 1; return []
        | otherwise = do UI s f <- get
                         let r = recoverable x y
                         let err = cantUnify from r
                                     topx topy (CantUnify r x y (Msg "") (errEnv env) s) (errEnv env) s
                         if (not r) then lift $ tfail err
                           else do put (UI s ((x, y, env, err, from, Unify) : f))
                                   return [] -- lift $ tfail err

    unApp fn bnames appx@(App fx ax) appy@(App fy ay)
         | (injectiveApp fx && injectiveApp fy)
        || (injectiveApp fx && rigid appx && metavarApp appy && numArgs appx == numArgs appy)
        || (injectiveApp fy && rigid appy && metavarApp appx && numArgs appx == numArgs appy)
        || (injectiveApp fx && metavarApp fy && ax == ay)
        || (injectiveApp fy && metavarApp fx && ax == ay)
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
       | otherwise = unifyTmpFail appx appy
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

            numArgs tm = let (f, args) = unApply tm in length args

            metavarApp tm = let (f, args) = unApply tm in
                                (metavar f &&
                                 all (\x -> metavarApp x) args
                                    && nub args == args) ||
                                       globmetavar tm
            metavarArgs tm = let (f, args) = unApply tm in
                                 all (\x -> metavar x || inenv x) args
                                   && nub args == args
            metavarApp' tm = let (f, args) = unApply tm in
                                 all (\x -> pat x || metavar x) (f : args)
                                   && nub args == args

            rigid (P (DCon _ _) _ _) = True
            rigid (P (TCon _ _) _ _) = True
            rigid t@(P Ref _ _)      = inenv t || globmetavar t
            rigid (Constant _)       = True
            rigid (App f a)          = rigid f && rigid a
            rigid t                  = not (metavar t) || globmetavar t

            globmetavar t = case unApply t  of
                                (P _ x _, _) ->
                                   case lookupDef x ctxt of
                                        [TyDecl _ _] -> True
                                        _ -> False
                                _ -> False

            metavar t = case t of
                             P _ x _ -> (x `elem` holes || holeIn env x)
                                          || globmetavar t
                             _ -> False
            pat t = case t of
                         P _ x _ -> x `elem` holes || patIn env x
                         _ -> False
            inenv t = case t of
                           P _ x _ -> x `elem` (map fst env)
                           _ -> False

            notFn t = injective t || metavar t || inenv t


    unifyTmpFail :: Term -> Term -> StateT UInfo TC [(Name, TT Name)]
    unifyTmpFail x y
                  = do UI s f <- get
                       let r = recoverable x y
                       let err = cantUnify from r
                                   topx topy (CantUnify r x y (Msg "") (errEnv env) s) (errEnv env) s
                       put (UI s ((topx, topy, env, err, from, Unify) : f))
                       return []

    -- shortcut failure, if we *know* nothing can fix it
    unifyFail x y = do UI s f <- get
                       let r = recoverable x y
                       let err = cantUnify from r
                                   topx topy (CantUnify r x y (Msg "") (errEnv env) s) (errEnv env) s
                       put (UI s ((topx, topy, env, err, from, Unify) : f))
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
                       let err = cantUnify from r topx topy
                                   (CantUnify r (binderTy x) (binderTy y) (Msg "") (errEnv env) s)
                                   (errEnv env) s
                       put (UI s ((binderTy x, binderTy y, env, err, from, Unify) : f))
                       return [] -- lift $ tfail err

    checkCycle ns p@(x, P _ _ _) = return [p]
    checkCycle ns (x, tm)
        | not (x `elem` freeNames tm) = checkScope ns (x, tm)
        | otherwise = lift $ tfail (InfiniteUnify x tm (errEnv env))

    checkScope ns (x, tm) =
--           case boundVs (envPos x 0 env) tm of
--                [] -> return [(x, tm)]
--                (i:_) -> lift $ tfail (UnifyScope x (fst (fst (ns!!i)))
--                                      (inst ns tm) (errEnv env))
        let v = highV (-1) tm in
            if v >= length ns
               then lift $ tfail (Msg "SCOPE ERROR")
               else return [(x, bind v ns tm)]
      where inst [] tm = tm
            inst (((n, _), _) : ns) tm = inst ns (substV (P Bound n Erased) tm)

    bind i ns tm 
      | i < 0 = tm
      | otherwise = let ((x,y),ty) = ns!!i in
                        App (Bind y (Lam ty) (bind (i-1) ns tm))
                            (P Bound x ty)

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
boundVs i (V j) | j < i = []
                | otherwise = [j]
boundVs i (Bind n b sc) = boundVs (i + 1) sc
boundVs i (App f x) = let fs = boundVs i f
                          xs = boundVs i x in
                          nub (fs ++ xs)
boundVs i _ = []

highV :: Int -> Term -> Int
highV i (V j) | j > i = j
                | otherwise = i
highV i (Bind n b sc) = maximum [i, highV i (binderTy b), (highV i sc - 1)]
highV i (App f x) = max (highV i f) (highV i x)
highV i _ = i

envPos x i [] = 0
envPos x i ((y, _) : ys) | x == y = i
                         | otherwise = envPos x (i + 1) ys


-- If there are any clashes of constructors, deem it unrecoverable, otherwise some
-- more work may help.
-- FIXME: Depending on how overloading gets used, this may cause problems. Better
-- rethink overloading properly...

recoverable t@(App _ _) _
    | (P _ (UN l) _, _) <- unApply t, l == txt "Lazy" = False
recoverable _ t@(App _ _)
    | (P _ (UN l) _, _) <- unApply t, l == txt "Lazy" = False
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

