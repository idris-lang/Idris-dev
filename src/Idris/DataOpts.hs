{-# LANGUAGE PatternGuards #-}

module Idris.DataOpts where

-- Forcing, detagging and collapsing

import Idris.AbsSyntax
import Idris.AbsSyntaxTree
import Core.TT

import qualified Data.IntMap.Strict as IM
import Data.IntMap.Strict (IntMap)
import qualified Data.Map as M
import Data.Map (Map)
import Data.List
import Data.Maybe
import Debug.Trace

-- Calculate the forceable arguments to a constructor
-- and update the set of optimisations.
forceArgs :: Name -> Name -> Type -> Idris ()
forceArgs typeName n t = do
    ist <- getIState
    let fargs = replace () $ getForcedArgs ist typeName t
        copt = case lookupCtxt n (idris_optimisation ist) of
          []   -> Optimise False False (W IM.empty) []
          op:_ -> op
        opts = addDef n (copt { forceable = W fargs }) (idris_optimisation ist)
    putIState (ist { idris_optimisation = opts })
    addIBC (IBCOpt n)
    iLOG $ "Forced: " ++ show n ++ " " ++ show fargs ++ "\n   from " ++ show t
  where
    replace :: b -> ForceMap' a -> ForceMap' b
    replace x = M.map (fmap $ const x)

getForcedArgs :: IState -> Name -> Type -> ForceMap
getForcedArgs ist typeName t = addCollapsibleArgs 0 t $ forcedInTarget 0 t
  where
    maxUnion = IM.unionWith max

    -- Label all occurrences of the variable bound in Pi in the rest of
    -- the term with the number i so that we can recognize them anytime later.
    label i = instantiate $ P Bound (MN i "ctor_arg") Erased

    addCollapsibleArgs :: Int -> Type -> ForceMap -> ForceMap
    addCollapsibleArgs i (Bind vn (Pi ty) rest) alreadyForceable
        = addCollapsibleArgs (i+1) (label i rest) (forceable $ unApply ty)
      where
        forceable (P _ tn _, args)
            -- if `ty' is collapsible, the argument is unconditionally forceable
            | isCollapsible tn
            = IM.insert i Forceable alreadyForceable

            | tn == typeName
            -- a recursive occurrence with known indices is conditionally forceable
            = IM.insertWith max i CondForceable
                -- and it can also force variables guarded in its indices
                (unionMap guardedArgs args `maxUnion` alreadyForceable)

        forceable _ = alreadyForceable

        isCollapsible :: Name -> Bool
        isCollapsible n = case lookupCtxt n (idris_optimisation ist) of
            [oi] -> collapsible oi
            _    -> False

    addCollapsibleArgs _ _ fs = fs

    forcedInTarget :: Int -> Type -> ForceMap
    forcedInTarget i (Bind _ (Pi _) rest) = forcedInTarget (i+1) (label i rest)
    forcedInTarget i t@(App f a) | (_, as) <- unApply t = unionMap guardedArgs as
    forcedInTarget _ _ = IM.empty

    guardedArgs :: Term -> ForceMap
    guardedArgs t@(App f a) | (P (DCon _ _) _ _, args) <- unApply t
        = unionMap bareArg args `maxUnion` unionMap guardedArgs args
    guardedArgs t = bareArg t

    bareArg :: Term -> ForceMap
    bareArg (P _ (MN i "ctor_arg") _) = IM.singleton i Forceable
    bareArg  _                        = IM.empty

    unionMap :: (a -> ForceMap) -> [a] -> ForceMap
    unionMap f = IM.unionsWith max . map f

-- Calculate whether a collection of constructors is collapsible
-- and update the state accordingly.
collapseCons :: Name -> [(Name, Type)] -> Idris ()
collapseCons tn ctors = do
    ist <- getIState
    case ctors of
        _
          | all (>= CondForceable) (IM.elems $ forceMap tn ist)
          , disjointTerms ctorTargetArgs
            -> mapM_ setCollapsible (tn : map fst ctors)

        [(cn, ct)]
            -> checkNewType ist cn ct

        _ -> return () -- nothing can be done
  where
    --- [(name, [types of arguments w/o their names])]
    ctorArgs = map (\(n, t) -> (n, map snd (getArgTys t))) ctors
    ctorTargetArgs = map (snd . unApply . getRetTy . snd) ctors

    forceMap :: Name -> IState -> ForceMap
    forceMap n ist = case lookupCtxt n (idris_optimisation ist) of
        (oi:_) -> unW $ forceable oi
        _      -> IM.empty

    -- one constructor; if one remaining argument, treat as newtype
    checkNewType :: IState -> Name -> Type -> Idris ()
    checkNewType ist cn ct
        | oi:_ <- lookupCtxt cn opt
        , length (getArgTys ct) == 1 + IM.size (unW $ forceable oi)
            = putIState ist{ idris_optimisation = opt' oi }
        | otherwise = return ()
      where
        opt = idris_optimisation ist
        opt' oi = addDef cn oi{ isnewtype = True } opt

    setCollapsible :: Name -> Idris ()
    setCollapsible n
       = do i <- getIState
            iLOG $ show n ++ " collapsible"
            case lookupCtxt n (idris_optimisation i) of
               (oi:_) -> do let oi' = oi { collapsible = True }
                            let opts = addDef n oi' (idris_optimisation i)
                            putIState (i { idris_optimisation = opts })
               [] -> do let oi = Optimise True False (W IM.empty) []
                        let opts = addDef n oi (idris_optimisation i)
                        putIState (i { idris_optimisation = opts })
                        addIBC (IBCOpt n)

    disjointTerms :: [[Term]] -> Bool
    disjointTerms []         = True
    disjointTerms [xs]       = True
    disjointTerms (xs : xss) =
        -- xs is disjoint with every pattern from xss
        all (or . zipWith disjoint xs) xss
        -- and xss is pairwise disjoint, too
        && disjointTerms xss

    -- Return True  if the two patterns are provably disjoint.
    -- Return False if they're not or if unsure.
    disjoint :: Term -> Term -> Bool
    disjoint x y = case (cx, cy) of
        -- data constructors -> compare their names
        (P (DCon _ _) nx _, P (DCon _ _) ny _)
            | nx /= ny  -> True
            | otherwise -> or $ zipWith disjoint xargs yargs
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

forcedArgSeq :: OptInfo -> [Bool]
forcedArgSeq oi = map (isForced oi) [0..]
  where
    isForced oi i 
        -- We needn't consider CondForceable because it's only important when the type
        -- is collapsible -- but in that case this whole optimisation is irrelevant
        | Just f <- IM.lookup i (unW $ forceable oi) = f == Forceable
        | otherwise = False

applyDataOpt :: OptInfo -> Name -> [Raw] -> Raw
applyDataOpt oi n args 
    = raw_apply (Var n) $ zipWith doForce (forcedArgSeq oi) args
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
    | length args == arity = doOpts n args (collapsible oi) (unW $ forceable oi)
    | otherwise = let extra = satArgs (arity - length args)
                      tm = doOpts n (args ++ map (\n -> P Bound n Erased) extra)
                                    (collapsible oi) (unW $ forceable oi) in
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

    doOpts n args True _  = Erased
    doOpts n args _ forceMap
        | isnewtype oi = case args' of
            [val] -> val
            _ -> error "Can't happen (newtype not a singleton)"
        | otherwise = mkApp ctor' args'
      where
        ctor' = (P (DCon tag (arity - IM.size forceMap)) n Erased)
        args' = map snd . filter keep $ zip (forcedArgSeq oi) args

    keep (forced, _) = not forced

reconstructCollapsed :: Either Term (Term, Term) -> Idris (Either Term (Term, Term))
reconstructCollapsed (Left t) = return $ Left t  -- TODO: what's this?
reconstructCollapsed (Right (p, t)) = do
        ist <- getIState
        let ns = erasedNames ist p
        return $ Right (p, replaceReconstrs ns t)
  where
    erasedNames :: IState -> Term -> Map Name Term

    -- TODO: are these cases correctly empty?
    erasedNames ist (P nt n _) = M.empty
    erasedNames ist (V n)      = M.empty

    -- introductory pattern vars: pat x. T
    erasedNames ist (Bind n (PVar _) t)
        = erasedNames ist $ instantiate (P Bound n Erased) t

    -- todo: if the whole type of the ctor is collapsible, we shouldn't do anything here
    erasedNames ist app@(App f x)
        | (P (DCon _ _) n _, args) <- unApply app
            = M.unions $ map traverseArgs (zip [0..] args)
        | otherwise = erasedNames ist f `M.union` erasedNames ist x
      where
        forceMap = forceables ist n

        traverseArgs :: Int -> Term -> Map Name Term
        traverseArgs i t
            | Just (Forceable reconstr) <- IM.lookup i forceMap
                -- note that mkLazy gets inserted by replaceReconstrs
                = let recon = reconstr i args in case t of
                    -- bare variable, just reconstruct it
                    P Bound vn Erased ->
                        M.insert vn recon
                    -- we need to create a let-binding for every sub-variable
                    pat -> error $ "pattern-matching an erased term: " ++ pat
            | otherwise = erasedNames ist t

    erasedNames ist p = ("[unhandled]---->", p) `traceShow` M.empty

    -- TODO: don't forget to insert mkLazy around every replacement
    replaceReconstrs :: Map Name Term -> Term -> Term
    replaceReconstrs m t = m `traceShow` t

    forceables :: IState -> Name -> ForceMap
    forceables ist n = case lookupCtxt n (idris_optimisation ist) of
        [oi] -> forceable oi
        _    -> IM.empty
