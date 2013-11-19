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

forceArgs :: Name -> Name -> Type -> Idris ()
forceArgs tn n t = do
    ist <- getIState
    let fargs = forceableArgs ist t []
        copt  = case lookupCtxt n (idris_optimisation ist) of
          []     -> Optimise False False [] []
          (op:_) -> op
        opts = addDef n (copt { forceable = fargs }) (idris_optimisation ist)
    putIState (ist { idris_optimisation = opts })
    addIBC (IBCOpt n)
    iLOG $ "Forced: " ++ show n ++ " " ++ show fargs ++ "\n   from " ++ show t
  where
    forceableArgs :: IState -> Type -> [Int] -> [Int]
    forceableArgs ist t prevIxs
        | all (`elem` prevIxs) ixs = prevIxs
        | otherwise = forceableArgs ist t' (nub $ prevIxs ++ ixs)
      where
        (ixs, t') = force ist 0 t t

    force :: IState -> Int -> Type -> Type -> ([Int], Type)
    force ist i (Bind n (Pi ty) sc) whole
        | isCollapsible = (nub (i : ixs), whole')
        | otherwise     = (         ixs , whole')
      where
        isCollapsible = collapsibleIn ist ty
        (ixs, whole') = force ist (i+1) (eraseIn sc) (eraseIn whole)
        eraseIn       = instantiate $ P Bound (MN i erasedName) Erased
        erasedName    = if isCollapsible then "?forced" else "?"

    force _ _ sc@(App f a) whole
        = (ixs, foldr (.) id (map erase ixs) whole)
      where
        erase i = instantiate $ P Bound (MN i "?forced") Erased
        ixs = nub $ concatMap guarded args
        (_, args) = unApply sc

    force _ _ _ whole = ([], whole)

    collapsibleIn :: IState -> Type -> Bool
    collapsibleIn ist t = case unApply t of
        (P _ n' _, args)
            -- recursive applications of the datatype: n' == tn
            | n' == tn -> ("--->", args, map known args) `traceShow` all known args
            | otherwise -> case lookupCtxt n' (idris_optimisation ist) of
                [oi] -> collapsible oi
                _    -> False
        _ -> False

    -- somehow it marks (U xs) as known although xs is not known

    known :: Term -> Bool
    known (P Bound (MN _ "?forced") Erased) = True  -- erased data is trivially known
    known (P (DCon _ _) _ _) = True  -- data constructors are known
    known (P (TCon _ _) _ _) = True  -- type constructors are known
    -- what about (P Bound), (P Ref)?
    known (V _)        = False  -- references to previous non-erased fields are not known
    known (Bind _ _ _) = False  -- let's ignore binders, too
    known (App f x)    = known f && known x
    known (Constant _) = True
    known (Proj t _)   = known t
    known Erased       = True
    known Impossible   = True
    known (TType _)    = True
    known _            = False

    isF (P _ (MN force "?") _) = Just force
    isF _ = Nothing

    guarded :: Term -> [Int]
    guarded t@(App f a)
--         | (P (TCon _ _) _ _, args) <- unApply t
--             = mapMaybe isF args ++ concatMap guarded args
        | (P (DCon _ _) _ _, args) <- unApply t
            = mapMaybe isF args ++ concatMap guarded args
    guarded t = mapMaybe isF [t]

-- Calculate whether a collection of constructors is collapsible

collapseCons :: Name -> [(Name, Type)] -> Idris ()
collapseCons ty cons =
     do i <- getIState
        let cons' = map (\ (n, t) -> (n, map snd (getArgTys t))) cons
        allFR <- mapM (forceRec i) cons'
        if and allFR then detaggable (map getRetTy (map snd cons))
           else checkNewType cons'
  where
    -- one constructor; if one remaining argument, treat as newtype
    checkNewType [(n, ts)] = do
       i <- getIState
       case lookupCtxt n (idris_optimisation i) of
               (oi:_) -> do let remaining = length ts - length (forceable oi)
                            if remaining == 1 then
                               do let oi' = oi { isnewtype = True }
                                  let opts = addDef n oi' (idris_optimisation i)
                                  putIState (i { idris_optimisation = opts })
                               else return ()
               _ -> return ()

    checkNewType _ = return ()

    setCollapsible :: Name -> Idris ()
    setCollapsible n
       = do i <- getIState
            iLOG $ show n ++ " collapsible"
            case lookupCtxt n (idris_optimisation i) of
               (oi:_) -> do let oi' = oi { collapsible = True }
                            let opts = addDef n oi' (idris_optimisation i)
                            putIState (i { idris_optimisation = opts })
               [] -> do let oi = Optimise True False [] []
                        let opts = addDef n oi (idris_optimisation i)
                        putIState (i { idris_optimisation = opts })
                        addIBC (IBCOpt n)

    forceRec :: IState -> (Name, [Type]) -> Idris Bool
    forceRec i (n, ts)
       = case lookupCtxt n (idris_optimisation i) of
            (oi:_) -> checkFR (forceable oi) 0 ts
            _ -> return False

    checkFR fs i [] = return True
    checkFR fs i (_ : xs) | i `elem` fs = checkFR fs (i + 1) xs
    checkFR fs i (t : xs)
        -- must be recursive or type is not collapsible
        = do let (rtf, rta) = unApply $ getRetTy t
             if (ty `elem` freeNames rtf)
               then checkFR fs (i+1) xs
               else return False

    detaggable :: [Type] -> Idris ()
    detaggable rtys
        = do let rtyArgs = map (snd . unApply) rtys
             -- if every rtyArgs is disjoint with every other, it's detaggable,
             -- therefore also collapsible given forceable/recursive check
             if disjoint rtyArgs
                then mapM_ setCollapsible (ty : map fst cons)
                else return ()

    disjoint :: [[Term]] -> Bool
    disjoint []         = True
    disjoint [xs]       = True
    disjoint (xs : xss) =
        -- xs is disjoint with every pattern from xss
        all (or . zipWith disjointPair xs) xss
        -- and xss is pairwise disjoint, too
        && disjoint xss

    -- Return True  if the two patterns are provably disjoint.
    -- Return False if they're not or if unsure.
    disjointPair :: Term -> Term -> Bool
    disjointPair x y = case (cx, cy) of
        -- data constructors -> compare their names
        (P (DCon _ _) nx _, P (DCon _ _) ny _)
            | nx /= ny -> True
            | nx == ny -> and $ zipWith disjointPair xargs yargs
        _ -> False
      where
        (cx, xargs) = unApply x
        (cy, yargs) = unApply y

class Optimisable term where
    applyOpts :: term -> Idris term
    stripCollapsed :: term -> Idris term

instance (Optimisable a, Optimisable b) => Optimisable (a, b) where
    applyOpts (x, y) = do x' <- applyOpts x
                          y' <- applyOpts y
                          return (x', y')
    stripCollapsed (x, y) = do x' <- stripCollapsed x
                               y' <- stripCollapsed y
                               return (x', y')


instance (Optimisable a, Optimisable b) => Optimisable (vs, a, b) where
    applyOpts (v, x, y) = do x' <- applyOpts x
                             y' <- applyOpts y
                             return (v, x', y')
    stripCollapsed (v, x, y) = do x' <- stripCollapsed x
                                  y' <- stripCollapsed y
                                  return (v, x', y')

instance Optimisable a => Optimisable [a] where
    applyOpts = mapM applyOpts
    stripCollapsed = mapM stripCollapsed

instance Optimisable a => Optimisable (Either a (a, a)) where
    applyOpts (Left t) = do t' <- applyOpts t; return $ Left t'
    applyOpts (Right t) = do t' <- applyOpts t; return $ Right t'
    stripCollapsed (Left t) = do t' <- stripCollapsed t; return $ Left t'
    stripCollapsed (Right t) = do t' <- stripCollapsed t; return $ Right t'

-- Raw is for compile time optimisation (before type checking)
-- Term is for run time optimisation (after type checking, collapsing allowed)

-- Compile time: no collapsing

instance Optimisable Raw where
    applyOpts t@(RApp f a)
        | (Var n, args) <- raw_unapply t -- MAGIC HERE
            = do args' <- mapM applyOpts args
                 i <- getIState
                 case lookupCtxt n (idris_optimisation i) of
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

    stripCollapsed t = return t

instance Optimisable t => Optimisable (Binder t) where
    applyOpts (Let t v) = do t' <- applyOpts t
                             v' <- applyOpts v
                             return (Let t' v')
    applyOpts b = do t' <- applyOpts (binderTy b)
                     return (b { binderTy = t' })
    stripCollapsed (Let t v) = do t' <- stripCollapsed t
                                  v' <- stripCollapsed v
                                  return (Let t' v')
    stripCollapsed b = do t' <- stripCollapsed (binderTy b)
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
    applyOpts (P _ (NS (UN "plus") ["Nat","Prelude"]) _)
        = return (P Ref (UN "prim__addBigInt") Erased)
    applyOpts (P _ (NS (UN "mult") ["Nat","Prelude"]) _)
        = return (P Ref (UN "prim__mulBigInt") Erased)
    applyOpts (App (P _ (NS (UN "fromIntegerNat") ["Nat","Prelude"]) _) x)
        = applyOpts x
    applyOpts (P _ (NS (UN "fromIntegerNat") ["Nat","Prelude"]) _)
        = return (App (P Ref (NS (UN "id") ["Basics","Prelude"]) Erased) Erased)
    applyOpts (P _ (NS (UN "toIntegerNat") ["Nat","Prelude"]) _)
        = return (App (P Ref (NS (UN "id") ["Basics","Prelude"]) Erased) Erased)
    applyOpts c@(P (DCon t arity) n _)
        = do i <- getIState
             case lookupCtxt n (idris_optimisation i) of
                 (oi:_) -> return $ applyDataOptRT oi n t arity []
                 _ -> return c
    applyOpts t@(App f a)
        | (c@(P (DCon t arity) n _), args) <- unApply t
            = do args' <- mapM applyOpts args
                 i <- getIState
                 case lookupCtxt n (idris_optimisation i) of
                      (oi:_) -> do return $ applyDataOptRT oi n t arity args'
                      _ -> return (mkApp c args')
        | otherwise = do f' <- applyOpts f
                         a' <- applyOpts a
                         return (App f' a')
    applyOpts (Bind n b t) = do b' <- applyOpts b
                                t' <- applyOpts t
                                return (Bind n b' t')
    applyOpts (Proj t i) = do t' <- applyOpts t
                              return (Proj t' i)
    applyOpts t = return t

    stripCollapsed (Bind n (PVar x) t) | (P _ ty _, _) <- unApply x
           = do i <- getIState
                -- NOTE: This assumes that 'ty' is in normal form, which it
                -- has to be before now because we're not keeping track of
                -- an environment so we can't do it here.
                case lookupCtxt ty (idris_optimisation i) of
                  [oi] -> if collapsible oi
                             then do t' <- stripCollapsed t
                                     return (Bind n (PVar x) (instantiate Erased t'))
                             else do t' <- stripCollapsed t
                                     return (Bind n (PVar x) t')
                  _ -> do t' <- stripCollapsed t
                          return (Bind n (PVar x) t')
    stripCollapsed (Bind n (PVar x) t)
                  = do t' <- stripCollapsed t
                       return (Bind n (PVar x) t')
    stripCollapsed t = return t

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

    -- Nat special cases
    -- TODO: Would be nice if this was configurable in idris source!
    doOpts (NS (UN "Z") ["Nat", "Prelude"]) [] _ _ = Constant (BI 0)
    doOpts (NS (UN "S") ["Nat", "Prelude"]) [k] _ _
        = App (App (P Ref (UN "prim__addBigInt") Erased) k) (Constant (BI 1))

    doOpts n args True f = Erased
    doOpts n args _ forced
        = let args' = filter keep (zip (map (\x -> x `elem` forced) [0..])
                                       args) in
              if isnewtype oi
                then case args' of
                          [(_, val)] -> val
                          _ -> error "Can't happen (not isnewtype)"
                else
                  mkApp (P (DCon tag (arity - length forced)) n Erased)
                        (map snd args')

    keep (forced, _) = not forced


