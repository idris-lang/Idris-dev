{-# LANGUAGE PatternGuards #-}

module Idris.DataOpts where

-- Forcing, detagging and collapsing

import Idris.AbsSyntax
import Core.TT

import qualified Data.IntSet as S
import Data.IntSet (IntSet)
import Data.List
import Data.Maybe
import Debug.Trace

-- Calculate the forceable arguments to a constructor and update the set of
-- optimisations

forceArgs :: Name -> Name -> Type -> Idris ()
forceArgs typeName n t = do
    ist <- getIState
    let fargs = S.toList $ forceableArgs ist t S.empty
        copt  = case lookupCtxt n (idris_optimisation ist) of
          []     -> Optimise False False [] []
          (op:_) -> op
        opts = addDef n (copt { forceable = fargs }) (idris_optimisation ist)
    putIState (ist { idris_optimisation = opts })
    addIBC (IBCOpt n)
    iLOG $ "Forced: " ++ show n ++ " " ++ show fargs ++ "\n   from " ++ show t
  where
    -- Calculate the indices of forceable arguments from a type of a data constructor.
    forceableArgs :: IState -> Type -> IntSet -> IntSet
    forceableArgs ist t alreadyForceable
        | forceable `S.isSubsetOf` alreadyForceable = forceable  -- no more indices, stop iterating
        | otherwise = forceableArgs ist t (forceable `S.union` alreadyForceable)
      where
        forceable = force ist 0 t alreadyForceable

    force :: IState -> Int -> Type -> IntSet -> IntSet
    force ist i (Bind n (Pi ty) sc) alreadyForceable
        = force ist (i+1) (labelIn sc) forceable
      where
        -- Label all occurrences of the variable bound in Pi in the rest of
        -- the term with the number i so that we can recognize them anytime later.
        labelIn = instantiate $ P Bound (MN i "ctor_arg") Erased

        forceable
            | -- if `ty' is collapsible, the argument is forceable
              ty `collapsibleIn` ist  
              -- a recursive occurrence with known indices is "forceable"
              || knownRecursive ty alreadyForceable    
                = S.insert i alreadyForceable
            | otherwise = alreadyForceable

    -- constructor target
    force _ _ sc@(App f a) alreadyForceable
        = alreadyForceable `S.union` unionMap guardedArgs args
      where
        (_, args) = unApply sc

    force _ _ _ forceable = forceable
    
    knownRecursive :: Type -> IntSet -> Bool
    knownRecursive t forceable = case unApply t of
        (P _ n _, args) -> n == typeName && all (known forceable) args
        _ -> False

    collapsibleIn :: Type -> IState -> Bool
    t `collapsibleIn` ist = case unApply t of
        (P _ n _, _) -> case lookupCtxt n (idris_optimisation ist) of
            [oi] -> collapsible oi
            _    -> False
        _ -> False

    -- This predicate does not cover all known terms;
    -- hopefully it does not cover any not-known terms.
    known :: IntSet -> Term -> Bool
    known forceable (P Bound (MN i "ctor_arg") Erased)
        = i `S.member` forceable  -- forceable data is known
    known _ (P (DCon _ _) _ _) = True  -- data constructors are known
    known _ (P (TCon _ _) _ _) = True  -- type constructors are known
    -- what about (P Bound), (P Ref)?
    known _ (V _)        = False
    known _ (Bind _ _ _) = False  -- let's ignore binders, too
    known f (App g x)    = known f g && known f x
    known _ (Constant _) = True
    known f (Proj t _)   = known f t
    known _ Erased       = True
    known _ Impossible   = True
    known _ (TType _)    = True
    known _ _            = False

    -- Return the indices of all constructor arguments
    -- referenced to in the term.
    ctorArgs :: Term -> IntSet
    ctorArgs (P _ (MN i "ctor_arg") _) = S.singleton i
    ctorArgs _ = S.empty

    guardedArgs :: Term -> IntSet
    guardedArgs t@(App f a) | (P (DCon _ _) _ _, args) <- unApply t
        = unionMap ctorArgs args `S.union` unionMap guardedArgs args
    guardedArgs t = ctorArgs t

    unionMap :: (a -> IntSet) -> [a] -> IntSet
    unionMap f xs = S.unions $ map f xs

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


