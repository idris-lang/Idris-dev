{-|
Module      : Idris.Core.Unify
Description : Idris' unification code.
Copyright   :
License     : BSD3
Maintainer  : The Idris Community.

Unification is applied inside the theorem prover. We're looking for holes
which can be filled in, by matching one term's normal form against another.
Returns a list of hole names paired with the term which solves them, and
a list of things which need to be injective.

-}
{-# LANGUAGE PatternGuards #-}

module Idris.Core.Unify(
    match_unify, unify
  , Fails, FailContext(..), FailAt(..)
  , unrecoverable
  ) where

import Idris.Core.Evaluate
import Idris.Core.TT

import Control.Monad
import Control.Monad.State.Strict
import Data.List
import Data.Maybe
import Debug.Trace

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
type Fails = [(TT Name, TT Name, -- unification error
               Bool, -- ready to retry yet
               Env, Err, [FailContext], FailAt)]

unrecoverable :: Fails -> Bool
unrecoverable = any bad
  where bad (_,_,_,_, err, _, _) = unrec err

        unrec (CantUnify r _ _ _ _ _) = not r
        unrec (At _ e) = unrec e
        unrec (Elaborating _ _ _ e) = unrec e
        unrec (ElaboratingArg _ _ _ e) = unrec e
        unrec _ = False

data UInfo = UI Int Fails
     deriving Show

data UResult a = UOK a
               | UPartOK a
               | UFail Err

-- | Smart constructor for unification errors that takes into account the FailContext
cantUnify :: [FailContext] -> Bool -> (t, Maybe Provenance) -> (t, Maybe Provenance) -> (Err' t) -> [(Name, t)] -> Int -> Err' t
cantUnify [] r t1 t2 e ctxt i = CantUnify r t1 t2 e ctxt i
cantUnify (FailContext fc f x : prev) r t1 t2 e ctxt i =
  At fc (ElaboratingArg f x
          (map (\(FailContext _ f' x') -> (f', x')) prev)
          (CantUnify r t1 t2 e ctxt i))

-- Solve metavariables by matching terms against each other
-- Not really unification, of course!

match_unify :: Context -> Env ->
               (TT Name, Maybe Provenance) ->
               (TT Name, Maybe Provenance) -> [Name] -> [Name] -> [FailContext] ->
               TC [(Name, TT Name)]
match_unify ctxt env (topx, xfrom) (topy, yfrom) inj holes from =
     case runStateT (un [] (renameBindersTm env topx)
                           (renameBindersTm env topy)) (UI 0 []) of
        OK (v, UI _ []) ->
           do v' <- trimSolutions (topx, xfrom) (topy, yfrom) from env v
              return (map (renameBinders env) v')
        res ->
               let topxn = renameBindersTm env (normalise ctxt env topx)
                   topyn = renameBindersTm env (normalise ctxt env topy) in
                     case runStateT (un [] topxn topyn)
                                (UI 0 []) of
                       OK (v, UI _ fails) ->
                            do v' <- trimSolutions (topx, xfrom) (topy, yfrom) from env v
                               return (map (renameBinders env) v')
                       Error e ->
                        -- just normalise the term we're matching against
                         case runStateT (un [] topxn topy)
                                  (UI 0 []) of
                           OK (v, UI _ fails) ->
                              do v' <- trimSolutions (topx, xfrom) (topy, yfrom) from env v
                                 return (map (renameBinders env) v')
                           _ -> tfail e
  where
    un :: [((Name, Name), TT Name)] -> TT Name -> TT Name ->
          StateT UInfo
          TC [(Name, TT Name)]

    un names tx@(P _ x _) tm
        | tx /= tm && holeIn env x || x `elem` holes
            = do sc 1; checkCycle names tx (x, tm)
    un names tm ty@(P _ y _)
        | ty /= tm && holeIn env y || y `elem` holes
            = do sc 1; checkCycle names ty (y, tm)
    un bnames (V i) (P _ x _)
        | length bnames > i,
          fst (fst (bnames!!i)) == x ||
          snd (fst (bnames!!i)) == x = do sc 1; return []
    un bnames (P _ x _) (V i)
        | length bnames > i,
          fst (fst (bnames!!i)) == x ||
          snd (fst (bnames!!i)) == x = do sc 1; return []
    un bnames (Bind x bx sx) (Bind y by sy) | notHole bx && notHole by
        = do h1 <- uB bnames bx by
             h2 <- un (((x, y), binderTy bx) : bnames) sx sy
             combine bnames h1 h2
    un names (App _ fx ax) (App _ fy ay)
        = do hf <- un names fx fy
             ha <- un names ax ay
             combine names hf ha
    un names x y
        | OK True <- convEq' ctxt holes x y = do sc 1; return []
        | otherwise = do UI s f <- get
                         let r = recoverable (normalise ctxt env x)
                                             (normalise ctxt env y)
                         let err = cantUnify from r
                                     (topx, xfrom) (topy, yfrom) (CantUnify r (x, Nothing) (y, Nothing) (Msg "") (errEnv env) s) (errEnv env) s
                         if (not r) then lift $ tfail err
                           else do put (UI s ((x, y, True, env, err, from, Match) : f))
                                   lift $ tfail err


    uB bnames (Let tx vx) (Let ty vy) = do h1 <- un bnames tx ty
                                           h2 <- un bnames vx vy
                                           combine bnames h1 h2
    uB bnames (Lam _ tx) (Lam _ ty) = un bnames tx ty
    uB bnames (Pi r i tx _) (Pi r' i' ty _) = un bnames tx ty
    uB bnames x y = do UI s f <- get
                       let r = recoverable (normalise ctxt env (binderTy x))
                                           (normalise ctxt env (binderTy y))
                       let err = cantUnify from r (topx, xfrom) (topy, yfrom)
                                   (CantUnify r (binderTy x, Nothing)
                                                (binderTy y, Nothing) (Msg "") (errEnv env) s)
                                   (errEnv env) s
                       put (UI s ((binderTy x, binderTy y,
                                   False,
                                   env, err, from, Match) : f))
                       return []

    notHole (Hole _) = False
    notHole _ = True

    -- TODO: there's an annoying amount of repetition between this and the
    -- main unification function. Consider lifting it out.
    -- Issue #1721 on the issue tracker: https://github.com/idris-lang/Idris-dev/issues/1721

    sc i = do UI s f <- get
              put (UI (s+i) f)

    unifyFail x y = do UI s f <- get
                       let r = recoverable (normalise ctxt env x)
                                           (normalise ctxt env y)
                       let err = cantUnify from r
                                   (topx, xfrom) (topy, yfrom)
                                   (CantUnify r (x, Nothing) (y, Nothing) (Msg "") (errEnv env) s) (errEnv env) s
                       put (UI s ((x, y, True, env, err, from, Match) : f))
                       lift $ tfail err
    combine bnames as [] = return as
    combine bnames as ((n, t) : bs)
        = case lookup n as of
            Nothing -> combine bnames (as ++ [(n,t)]) bs
            Just t' -> do ns <- un bnames t t'
                          let ns' = filter (\ (x, _) -> x/=n) ns
                          sc 1
                          combine bnames as (ns' ++ bs)

--     substN n tm (var, sol) = (var, subst n tm sol)

    checkCycle ns xtm p@(x, P _ x' _) | x == x' = return []
    checkCycle ns xtm p@(x, P _ _ _) = return [p]
    checkCycle ns xtm (x, tm)
        | conGuarded ctxt x tm = lift $ tfail (InfiniteUnify x tm (errEnv env))
        | x `elem` freeNames tm = unifyFail xtm tm
        | otherwise = checkScope ns (x, tm)

    checkScope ns (x, tm) =
--           case boundVs (envPos x 0 env) tm of
--                [] -> return [(x, tm)]
--                (i:_) -> lift $ tfail (UnifyScope x (fst (fst (ns!!i)))
--                                      (impl ns tm) (errEnv env))
        let v = highV (-1) tm in
            if v >= length ns
               then lift $ tfail (Msg "SCOPE ERROR")
               else return [(x, bind v ns tm)]
      where impl [] tm = tm
            impl ((n, _) : ns) tm = impl ns (substV (P Bound n Erased) tm)

    bind i ns tm
      | i < 0 = tm
      | otherwise = let ((x,y),ty) = ns!!i in
                        App MaybeHoles (Bind y (Lam RigW ty) (bind (i-1) ns tm))
                            (P Bound x ty)

renameBinders env (x, t) = (x, renameBindersTm env t)

renameBindersTm :: Env -> TT Name -> TT Name
renameBindersTm env tm = uniqueBinders (map fstEnv env) tm
  where
    uniqueBinders env (Bind n b sc)
        | n `elem` env
             = let n' = uniqueName n env in
                   explicitHole $ Bind n' (fmap (uniqueBinders env) b)
                           (uniqueBinders (n':env) (rename n n' sc))
        | otherwise = Bind n (fmap (uniqueBinders (n:env)) b)
                             (uniqueBinders (n:env) sc)
    uniqueBinders env (App s f a) = App s (uniqueBinders env f) (uniqueBinders env a)
    uniqueBinders env t = t

    rename n n' (P nt x ty) | n == x = P nt n' ty
    rename n n' (Bind x b sc) = Bind x (fmap (rename n n') b) (rename n n' sc)
    rename n n' (App s f a) = App s (rename n n' f) (rename n n' a)
    rename n n' t = t

    explicitHole (Bind n (Hole ty) sc)
       = Bind n (Hole ty) (instantiate (P Bound n ty) sc)
    explicitHole t = t

trimSolutions (topx, xfrom) (topy, yfrom) from env topns = followSols [] (dropPairs topns)
  where dropPairs [] = []
        dropPairs (n@(x, P _ x' _) : ns)
          | x == x' = dropPairs ns
          | otherwise
            = n : dropPairs
                    (filter (\t -> case t of
                                      (n, P _ n' _) -> not (n == x' && n' == x)
                                      _ -> True) ns)
        dropPairs (n : ns) = n : dropPairs ns

        followSols vs [] = return []
        followSols vs ((n, P _ t _) : ns)
          | Just t' <- lookup t ns
              = do vs' <- case t' of
                     P _ tn _ ->
                           if (n, tn) `elem` vs then -- cycle
                                   tfail (cantUnify from False (topx, xfrom) (topy, yfrom)
                                            (Msg "") (errEnv env) 0)
                                   else return ((n, tn) : vs)
                     _ -> return vs
                   followSols vs' ((n, t') : ns)
        followSols vs (n : ns) = do ns' <- followSols vs ns
                                    return $ n : ns'

expandLets env (x, tm) = (x, doSubst (reverse env) tm)
  where
    doSubst [] tm = tm
    doSubst ((n, Let v t) : env) tm
        = doSubst env (subst n v tm)
    doSubst (_ : env) tm
        = doSubst env tm

hasv :: TT Name -> Bool
hasv (V x) = True
hasv (App _ f a) = hasv f || hasv a
hasv (Bind x b sc) = hasv (binderTy b) || hasv sc
hasv _ = False

unify :: Context -> Env ->
         (TT Name, Maybe Provenance) ->
         (TT Name, Maybe Provenance) ->
         [Name] -> [Name] -> [Name] -> [FailContext] ->
         TC ([(Name, TT Name)], Fails)
unify ctxt env (topx, xfrom) (topy, yfrom) inj holes usersupp from =
--      traceWhen (hasv topx || hasv topy)
--           ("Unifying " ++ show topx ++ "\nAND\n" ++ show topy ++ "\n") $
             -- don't bother if topx and topy are different at the head
      case runStateT (un False [] (renameBindersTm env topx)
                                  (renameBindersTm env topy)) (UI 0 []) of
        OK (v, UI _ []) -> do v' <- trimSolutions (topx, xfrom) (topy, yfrom) from env v
                              return (map (renameBinders env) v', [])
        res ->
               let topxn = renameBindersTm env (normalise ctxt env topx)
                   topyn = renameBindersTm env (normalise ctxt env topy) in
--                     trace ("Unifying " ++ show (topx, topy) ++ "\n\n==>\n" ++ show (topxn, topyn) ++ "\n\n") $
                     case runStateT (un False [] topxn topyn)
                                (UI 0 []) of
                       OK (v, UI _ fails) ->
                            do v' <- trimSolutions (topx, xfrom) (topy, yfrom) from env v
--                                trace ("OK " ++ show (topxn, topyn, v, holes)) $
                               return (map (renameBinders env) v', reverse fails)
--         Error e@(CantUnify False _ _ _ _ _)  -> tfail e
                       Error e -> tfail e
  where
    headDiff (P (DCon _ _ _) x _) (P (DCon _ _ _) y _) = x /= y
    headDiff (P (TCon _ _) x _) (P (TCon _ _) y _) = x /= y
    headDiff _ _ = False

    injective (P (DCon _ _ _) _ _) = True
    injective (P (TCon _ _) _ _) = True
--     injective (P Ref n _)
--          | Just i <- lookupInjectiveExact n ctxt = i
    injective (App _ f a)        = injective f -- && injective a
    injective _                  = False

--     injectiveTC (P Ref n _) (P Ref n' _)
--          | Just i <- lookupInjectiveExact n ctxt,
--            n == n' = i
--     injectiveTC (App _ f a) (App _ f' a') = injectiveTC f a
--     injectiveTC _ _ = False

--     injectiveVar (P _ (MN _ _) _) = True -- TMP HACK
    injectiveVar (P _ n _)        = n `elem` inj
    injectiveVar (App _ f a)      = injectiveVar f -- && injective a
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
    un = un' env
--     un fn names x y
--         = let (xf, _) = unApply x
--               (yf, _) = unApply y in
--               if headDiff xf yf then unifyFail x y else
--                   uplus (un' fn names x y)
--                         (un' fn names (hnf ctxt env x) (hnf ctxt env y))

    un' :: Env -> Bool -> [((Name, Name), TT Name)] -> TT Name -> TT Name ->
           StateT UInfo
           TC [(Name, TT Name)]
    un' env fn names x y | x == y = return [] -- shortcut
    un' env fn names topx@(P (DCon _ _ _) x _) topy@(P (DCon _ _ _) y _)
                | x /= y = unifyFail topx topy
    un' env fn names topx@(P (TCon _ _) x _) topy@(P (TCon _ _) y _)
                | x /= y = unifyFail topx topy
    un' env fn names topx@(P (DCon _ _ _) x _) topy@(P (TCon _ _) y _)
                = unifyFail topx topy
    un' env fn names topx@(P (TCon _ _) x _) topy@(P (DCon _ _ _) y _)
                = unifyFail topx topy
    un' env fn names topx@(Constant _) topy@(P (TCon _ _) y _)
                = unifyFail topx topy
    un' env fn names topx@(P (TCon _ _) x _) topy@(Constant _)
                = unifyFail topx topy
    un' env fn bnames tx@(P _ x _) ty@(P _ y _)
        | (x,y) `elem` map fst bnames || x == y = do sc 1; return []
        | injective tx && not (holeIn env y || y `elem` holes)
             = unifyTmpFail tx ty
        | injective ty && not (holeIn env x || x `elem` holes)
             = unifyTmpFail tx ty
        -- pick the one bound earliest if both are holes
        | tx /= ty && (holeIn env x || x `elem` holes)
                   && (holeIn env y || y `elem` holes)
            = case compare (envPos 0 x env) (envPos 0 y env) of
                   LT -> do sc 1; checkCycle bnames tx (x, ty)
                   _ -> do sc 1; checkCycle bnames ty (y, tx)
       where envPos i n ((n',_,_):env) | n == n' = i
             envPos i n (_:env) = envPos (i+1) n env
             envPos _ _ _ = 100000
    un' env fn bnames xtm@(P _ x _) tm
        | pureTerm tm, holeIn env x || x `elem` holes
                       = do UI s f <- get
                            -- injectivity check
                            x <- checkCycle bnames xtm (x, tm)
                            if (notP tm && fn)
--                               trace (show (x, tm, normalise ctxt env tm)) $
--                                 put (UI s ((tm, topx, topy) : i) f)
                                 then unifyTmpFail xtm tm
                                 else do sc 1
                                         return x
        | pureTerm tm, not (injective xtm) && injective tm
                       = do checkCycle bnames xtm (x, tm)
                            unifyTmpFail xtm tm
    un' env fn bnames tm ytm@(P _ y _)
        | pureTerm tm, holeIn env y || y `elem` holes
                       = do UI s f <- get
                            -- injectivity check
                            x <- checkCycle bnames ytm (y, tm)
                            if (notP tm && fn)
--                               trace (show (y, tm, normalise ctxt env tm)) $
--                                 put (UI s ((tm, topx, topy) : i) f)
                                 then unifyTmpFail tm ytm
                                 else do sc 1
                                         return x
        | pureTerm tm, not (injective ytm) && injective tm
                       = do checkCycle bnames ytm (y, tm)
                            unifyTmpFail tm ytm
    un' env fn bnames (V i) (P _ x _)
        | length bnames > i,
          fst ((map fst bnames)!!i) == x ||
          snd ((map fst bnames)!!i) == x = do sc 1; return []
    un' env fn bnames (P _ x _) (V i)
        | length bnames > i,
          fst ((map fst bnames)!!i) == x ||
          snd ((map fst bnames)!!i) == x = do sc 1; return []

    un' env fn names topx@(Bind n (Hole t) sc) y = unifyTmpFail topx y
    un' env fn names x topy@(Bind n (Hole t) sc) = unifyTmpFail x topy

-- Pattern unification rule
    un' env fn bnames tm app@(App _ _ _)
        | (mvtm@(P _ mv _), args) <- unApply app,
          holeIn env mv || mv `elem` holes,
          all rigid args,
          containsOnly (mapMaybe getname args) (mapMaybe getV args) tm
          -- && TODO: tm does not refer to any variables other than those
          -- in 'args'
        = -- trace ("PATTERN RULE SOLVE: " ++ show (mv, tm, env, bindLams args (substEnv env tm))) $
          checkCycle bnames mvtm (mv, eta [] $ bindLams args (substEnv env tm))
      where rigid (V i) = True
            rigid (P _ t _) = t `elem` map fstEnv env &&
                              not (holeIn env t || t `elem` holes)
            rigid _ = False

            getV (V i) = Just i
            getV _ = Nothing

            getname (P _ n _) = Just n
            getname _ = Nothing

            containsOnly args vs (V i) = i `elem` vs
            containsOnly args vs (P Bound n ty)
                   = n `elem` args && containsOnly args vs ty
            containsOnly args vs (P _ n ty)
                   = not (holeIn env n || n `elem` holes)
                        && containsOnly args vs ty
            containsOnly args vs (App _ f a)
                   = containsOnly args vs f && containsOnly args vs a
            containsOnly args vs (Bind _ b sc)
                   = containsOnly args vs (binderTy b) &&
                     containsOnly args (0 : map (+1) vs) sc
            containsOnly args vs _ = True

            bindLams [] tm = tm
            bindLams (a : as) tm = bindLam a (bindLams as tm)

            bindLam (V i) tm = Bind (fstEnv (env !! i))
                                    (Lam RigW (binderTy (sndEnv (env !! i))))
                                    tm
            bindLam (P _ n ty) tm = Bind n (Lam RigW ty) tm
            bindLam _ tm = error "Can't happen [non rigid bindLam]"

            substEnv [] tm = tm
            substEnv ((n, _, t) : env) tm
                = substEnv env (substV (P Bound n (binderTy t)) tm)

            -- remove any unnecessary lambdas (helps with interface
            -- resolution later).
            eta ks (Bind n (Lam r ty) sc) = eta ((n, r, ty) : ks) sc
            eta ks t = rebind ks t

            rebind ((n, r, ty) : ks) (App _ f (P _ n' _))
                | n == n' = eta ks f
            rebind ((n, r, ty) : ks) t = rebind ks (Bind n (Lam r ty) t)
            rebind _ t = t

    un' env fn bnames appx@(App _ _ _) appy@(App _ _ _)
        = unApp env fn bnames appx appy
--         = uplus (unApp fn bnames appx appy)
--                 (unifyTmpFail appx appy) -- take the whole lot

    un' env fn bnames x (Bind n (Lam _ t) (App _ y (P Bound n' _)))
        | n == n' = un' env False bnames x y
    un' env fn bnames (Bind n (Lam _ t) (App _ x (P Bound n' _))) y
        | n == n' = un' env False bnames x y
    un' env fn bnames x (Bind n (Lam _ t) (App _ y (V 0)))
        = un' env False bnames x y
    un' env fn bnames (Bind n (Lam _ t) (App _ x (V 0))) y
        = un' env False bnames x y
--     un' env fn bnames (Bind x (PVar _) sx) (Bind y (PVar _) sy)
--         = un' env False ((x,y):bnames) sx sy
--     un' env fn bnames (Bind x (PVTy _) sx) (Bind y (PVTy _) sy)
--         = un' env False ((x,y):bnames) sx sy

    -- f D unifies with t -> D. This is dubious, but it helps with
    -- interface resolution for interfaces over functions.

    un' env fn bnames (App _ f x) (Bind n (Pi r i t k) y)
      | noOccurrence n y && injectiveApp f
        = do ux <- un' env False bnames x y
             uf <- un' env False bnames f (Bind (sMN 0 "uv") (Lam RigW (TType (UVar [] 0)))
                                      (Bind n (Pi r i t k) (V 1)))
             combine env bnames ux uf

    un' env fn bnames (Bind n (Pi r i t k) y) (App _ f x)
      | noOccurrence n y && injectiveApp f
        = do ux <- un' env False bnames y x
             uf <- un' env False bnames (Bind (sMN 0 "uv") (Lam RigW (TType (UVar [] 0)))
                                    (Bind n (Pi r i t k) (V 1))) f
             combine env bnames ux uf

    un' env fn bnames (Bind x bx sx) (Bind y by sy)
        | sameBinder bx by
           = do h1 <- uB env bnames bx by
                h2 <- un' ((x, RigW, bx) : env) False (((x,y),binderTy bx):bnames) sx sy
                combine env bnames h1 h2
      where sameBinder (Lam _ _) (Lam _ _) = True
            sameBinder (Pi _ i _ _) (Pi _ i' _ _) = True
            sameBinder _ _ = False -- never unify holes/guesses/etc
    un' env fn bnames x y
        | OK True <- convEq' ctxt holes x y = do sc 1; return []
        | isUniverse x && isUniverse y = do sc 1; return []
        | otherwise = do UI s f <- get
                         let r = recoverable (normalise ctxt env x)
                                             (normalise ctxt env y)
                         let err = cantUnify from r
                                     (topx, xfrom) (topy, yfrom) (CantUnify r (x, Nothing) (y, Nothing) (Msg "") (errEnv env) s) (errEnv env) s
                         if (not r) then lift $ tfail err
                           else do put (UI s ((x, y, True, env, err, from, Unify) : f))
                                   return [] -- lift $ tfail err

    unApp env fn bnames appx@(App _ fx ax) appy@(App _ fy ay)
        -- shortcut for the common case where we just want to check the
        -- arguments are correct
         | (injectiveApp fx && fx == fy)
         = un' env False bnames ax ay
         | (injectiveApp fx && injectiveApp fy)
        || (injectiveApp fx && metavarApp fy && ax == ay)
        || (injectiveApp fy && metavarApp fx && ax == ay)
        || (injectiveTC fx fy) -- data interface method
         = do let (headx, _) = unApply fx
              let (heady, _) = unApply fy
              -- fail quickly if the heads are disjoint
              checkHeads headx heady
              uplus
                (do hf <- un' env True bnames fx fy
                    let ax' = hnormalise hf ctxt env (substNames hf ax)
                    let ay' = hnormalise hf ctxt env (substNames hf ay)
                    -- Don't normalise if we don't have to
                    ha <- uplus (un' env False bnames (substNames hf ax)
                                                      (substNames hf ay))
                                (un' env False bnames ax' ay')
                    sc 1
                    combine env bnames hf ha)
                (do ha <- un' env False bnames ax ay
                    let fx' = hnormalise ha ctxt env (substNames ha fx)
                    let fy' = hnormalise ha ctxt env (substNames ha fy)
                    -- Don't normalise if we don't have to
                    hf <- uplus (un' env False bnames (substNames ha fx)
                                                      (substNames ha fy))
                                (un' env False bnames fx' fy')
                    sc 1
                    combine env bnames hf ha)
       | otherwise = unifyTmpFail appx appy
      where hnormalise [] _ _ t = t
            hnormalise ns ctxt env t = normalise ctxt env t
            checkHeads (P (DCon _ _ _) x _) (P (DCon _ _ _) y _)
                | x /= y = unifyFail appx appy
            checkHeads (P (TCon _ _) x _) (P (TCon _ _) y _)
                | x /= y = unifyFail appx appy
            checkHeads (P (DCon _ _ _) x _) (P (TCon _ _) y _)
                = unifyFail appx appy
            checkHeads (P (TCon _ _) x _) (P (DCon _ _ _) y _)
                = unifyFail appx appy
            checkHeads _ _ = return []

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

            rigid (P (DCon _ _ _) _ _) = True
            rigid (P (TCon _ _) _ _) = True
            rigid t@(P Ref _ _)  = inenv t || globmetavar t
            rigid (Constant _)       = True
            rigid (App _ f a)        = rigid f && rigid a
            rigid t                  = not (metavar t) || globmetavar t

            globmetavar t = case unApply t  of
                                (P _ x _, _) ->
                                   case lookupDef x ctxt of
                                        [TyDecl _ _] -> True
                                        _ -> False
                                _ -> False

            metavar t = case t of
                             P _ x _ -> (x `notElem` usersupp &&
                                             (x `elem` holes || holeIn env x))
                                          || globmetavar t
                             _ -> False
            pat t = case t of
                         P _ x _ -> x `elem` holes || patIn env x
                         _ -> False
            inenv t = case t of
                           P _ x _ -> x `elem` (map fstEnv env)
                           _ -> False

            notFn t = injective t || metavar t || inenv t

            injectiveTC t@(P Ref n _) t'@(P Ref n' _)
                | Just ni <- lookupInjectiveExact n ctxt,
                  Just ni' <- lookupInjectiveExact n' ctxt
              = (n == n' && ni) ||
                (ni && metavar t') ||
                (metavar t && ni')
            injectiveTC (App _ f a) (App _ f' a') = injectiveTC f f'
            injectiveTC _ _ = False


    unifyTmpFail :: Term -> Term -> StateT UInfo TC [(Name, TT Name)]
    unifyTmpFail x y
                  = do UI s f <- get
                       let r = recoverable (normalise ctxt env x) (normalise ctxt env y)
                       let err = cantUnify from r
                                   (topx, xfrom) (topy, yfrom)
                                   (CantUnify r (x, Nothing) (y, Nothing) (Msg "") (errEnv env) s) (errEnv env) s
                       put (UI s ((topx, topy, True, env, err, from, Unify) : f))
                       return []

    -- shortcut failure, if we *know* nothing can fix it
    unifyFail x y = do UI s f <- get
                       let r = recoverable (normalise ctxt env x) (normalise ctxt env y)
                       let err = cantUnify from r
                                   (topx, xfrom) (topy, yfrom)
                                   (CantUnify r (x, Nothing) (y, Nothing) (Msg "") (errEnv env) s) (errEnv env) s
                       put (UI s ((topx, topy, True, env, err, from, Unify) : f))
                       lift $ tfail err


    uB env bnames (Let tx vx) (Let ty vy)
        = do h1 <- un' env False bnames tx ty
             h2 <- un' env False bnames vx vy
             sc 1
             combine env bnames h1 h2
    uB env bnames (Guess tx vx) (Guess ty vy)
        = do h1 <- un' env False bnames tx ty
             h2 <- un' env False bnames vx vy
             sc 1
             combine env bnames h1 h2
    uB env bnames (Lam _ tx) (Lam _ ty) = do sc 1; un' env False bnames tx ty
    uB env bnames (Pi _ _ tx _) (Pi _ _ ty _) = do sc 1; un' env False bnames tx ty
    uB env bnames (Hole tx) (Hole ty) = un' env False bnames tx ty
    uB env bnames (PVar _ tx) (PVar _ ty) = un' env False bnames tx ty
    uB env bnames x y
                  = do UI s f <- get
                       let r = recoverable (normalise ctxt env (binderTy x))
                                           (normalise ctxt env (binderTy y))
                       let err = cantUnify from r (topx, xfrom) (topy, yfrom)
                                   (CantUnify r (binderTy x, Nothing) (binderTy y, Nothing) (Msg "") (errEnv env) s)
                                   (errEnv env) s
                       put (UI s ((binderTy x, binderTy y,
                                   False,
                                   env, err, from, Unify) : f))
                       return [] -- lift $ tfail err

    checkCycle ns xtm p@(x, P _ _ _) = return [p]
    checkCycle ns xtm (x, tm)
        | conGuarded ctxt x tm = lift $ tfail (InfiniteUnify x tm (errEnv env))
        | x `elem` freeNames tm = unifyTmpFail xtm tm
        | otherwise = checkScope ns (x, tm)

    checkScope ns (x, tm) | pureTerm tm =
--           case boundVs (envPos x 0 env) tm of
--                [] -> return [(x, tm)]
--                (i:_) -> lift $ tfail (UnifyScope x (fst (fst (ns!!i)))
--                                      (impl ns tm) (errEnv env))
        let v = highV (-1) tm in
            if v >= length ns
               then lift $ tfail (Msg "SCOPE ERROR")
               else return [(x, bind v ns tm)]
      where impl [] tm = tm
            impl (((n, _), _) : ns) tm = impl ns (substV (P Bound n Erased) tm)
    checkScope ns (x, tm) = lift $ tfail (Msg "HOLE ERROR")

    bind i ns tm
      | i < 0 = tm
      | otherwise = let ((x,y),ty) = ns!!i in
                        App MaybeHoles (Bind y (Lam RigW ty) (bind (i-1) ns tm))
                            (P Bound x ty)

    combine env bnames as [] = return as
    combine env bnames as ((n, t) : bs)
        = case lookup n as of
            Nothing -> combine env bnames (as ++ [(n,t)]) bs
            Just t' -> do ns <- un' env False bnames t t'
                          -- make sure there's n mapping from n in ns
                          let ns' = filter (\ (x, _) -> x/=n) ns
                          sc 1
                          combine env bnames as (ns' ++ bs)

boundVs :: Int -> Term -> [Int]
boundVs i (V j) | j < i = []
                | otherwise = [j]
boundVs i (Bind n b sc) = boundVs (i + 1) sc
boundVs i (App _ f x) = let fs = boundVs i f
                            xs = boundVs i x in
                            nub (fs ++ xs)
boundVs i _ = []

highV :: Int -> Term -> Int
highV i (V j) | j > i = j
                | otherwise = i
highV i (Bind n b sc) = maximum [i, highV i (binderTy b), (highV i sc - 1)]
highV i (App _ f x) = max (highV i f) (highV i x)
highV i _ = i

envPos x i [] = 0
envPos x i ((y, _) : ys) | x == y = i
                         | otherwise = envPos x (i + 1) ys


-- If there are any clashes of constructors, deem it unrecoverable, otherwise some
-- more work may help.
-- FIXME: Depending on how overloading gets used, this may cause problems. Better
-- rethink overloading properly...
-- ASSUMPTION: inputs are in normal form
--
-- Issue #1722 on the issue tracker https://github.com/idris-lang/Idris-dev/issues/1722
--
recoverable t@(App _ _ _) _
    | (P _ (UN l) _, _) <- unApply t, l == txt "Delayed" = False
recoverable _ t@(App _ _ _)
    | (P _ (UN l) _, _) <- unApply t, l == txt "Delayed" = False
recoverable (P (DCon _ _ _) x _) (P (DCon _ _ _) y _) = x == y
recoverable (P (TCon _ _) x _) (P (TCon _ _) y _) = x == y
recoverable (TType _) (P (DCon _ _ _) y _) = False
recoverable (UType _) (P (DCon _ _ _) y _) = False
recoverable (Constant _) (P (DCon _ _ _) y _) = False
recoverable (Constant x) (Constant y) = x == y
recoverable (P (DCon _ _ _) x _) (TType _) = False
recoverable (P (DCon _ _ _) x _) (UType _) = False
recoverable (P (DCon _ _ _) x _) (Constant _) = False
recoverable (TType _) (P (TCon _ _) y _) = False
recoverable (UType _) (P (TCon _ _) y _) = False
recoverable (Constant _) (P (TCon _ _) y _) = False
recoverable (P (TCon _ _) x _) (TType _) = False
recoverable (P (TCon _ _) x _) (UType _) = False
recoverable (P (TCon _ _) x _) (Constant _) = False
recoverable (P (DCon _ _ _) x _) (P (TCon _ _) y _) = False
recoverable (P (TCon _ _) x _) (P (DCon _ _ _) y _) = False
recoverable p@(TType _) (App _ f a) = recoverable p f
recoverable p@(UType _) (App _ f a) = recoverable p f
recoverable p@(Constant _) (App _ f a) = recoverable p f
recoverable (App _ f a) p@(TType _) = recoverable f p
recoverable (App _ f a) p@(UType _) = recoverable f p
recoverable (App _ f a) p@(Constant _) = recoverable f p
recoverable p@(P _ n _) (App _ f a) = recoverable p f
recoverable (App _ f a) p@(P _ _ _) = recoverable f p
recoverable (App _ f a) (App _ f' a')
    | f == f' = recoverable a a'
recoverable (App _ f a) (App _ f' a')
    = recoverable f f' -- && recoverable a a'
recoverable f (Bind _ (Pi _ _ _ _) sc)
    | (P (DCon _ _ _) _ _, _) <- unApply f = False
    | (P (TCon _ _) _ _, _) <- unApply f = False
    | (Constant _) <- f = False
    | TType _ <- f = False
    | UType _ <- f = False
recoverable (Bind _ (Pi _ _ _ _) sc) f
    | (P (DCon _ _ _) _ _, _) <- unApply f = False
    | (P (TCon _ _) _ _, _) <- unApply f = False
    | (Constant _) <- f = False
    | TType _ <- f = False
    | UType _ <- f = False
recoverable (Bind _ (Lam _ _) sc) f = recoverable sc f
recoverable f (Bind _ (Lam _ _) sc) = recoverable f sc
recoverable x y = True

errEnv :: [(a, r, Binder b)] -> [(a, b)]
errEnv = map (\(x, _, b) -> (x, binderTy b))

holeIn :: Env -> Name -> Bool
holeIn env n = case lookupBinder n env of
                    Just (Hole _) -> True
                    Just (Guess _ _) -> True
                    _ -> False

patIn :: Env -> Name -> Bool
patIn env n = case lookupBinder n env of
                    Just (PVar _ _) -> True
                    Just (PVTy _) -> True
                    _ -> False
