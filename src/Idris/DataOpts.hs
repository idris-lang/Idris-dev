{-# LANGUAGE PatternGuards #-}

module Idris.DataOpts where

-- Forcing, detagging and collapsing

import Idris.AbsSyntax
import Idris.AbsSyntaxTree
import Idris.Core.TT

import Control.Applicative
import qualified Data.IntMap as M
import Data.List
import Data.Maybe
import Debug.Trace

type ForceMap = M.IntMap Forceability

-- Calculate the forceable arguments to a constructor
-- and update the set of optimisations.
forceArgs :: Name -> Name -> [Int] -> Type -> Idris ()
forceArgs typeName n expforce t = do
    ist <- getIState
    let fargs = getForcedArgs ist typeName t
        copt = case lookupCtxt n (idris_optimisation ist) of
          []   -> Optimise False False [] []
          op:_ -> op
        opts = addDef n (copt { forceable = M.toList fargs ++
                                            zip expforce (repeat Unconditional) }) 
                        (idris_optimisation ist)
    putIState (ist { idris_optimisation = opts })
    addIBC (IBCOpt n)
    iLOG $ "Forced: " ++ show n ++ " " ++ show fargs ++ "\n   from " ++ show t

getForcedArgs :: IState -> Name -> Type -> ForceMap
getForcedArgs ist typeName t = addCollapsibleArgs 0 t $ forcedInTarget 0 t
  where
    maxUnion = M.unionWith max

    -- Label all occurrences of the variable bound in Pi in the rest of
    -- the term with the number i so that we can recognize them anytime later.
    label i = instantiate $ P Bound (sMN i "ctor_arg") Erased

    addCollapsibleArgs :: Int -> Type -> ForceMap -> ForceMap
    addCollapsibleArgs i (Bind vn (Pi ty) rest) alreadyForceable
        = addCollapsibleArgs (i+1) (label i rest) (forceable $ unApply ty)
      where
        -- forceable takes an un-applied type of a ctor argument
        forceable (P _ tn _, args)
            -- if `ty' is collapsible, the argument is unconditionally forceable
            | isCollapsible tn
            = M.insert i Unconditional alreadyForceable

            -- a recursive occurrence with known indices is conditionally forceable
            | tn == typeName
            = M.insertWith max i Conditional alreadyForceable

        forceable _ = alreadyForceable

        isCollapsible :: Name -> Bool
        isCollapsible n = case lookupCtxt n (idris_optimisation ist) of
            [oi] -> collapsible oi
            _    -> False

    addCollapsibleArgs _ _ fs = fs

    forcedInTarget :: Int -> Type -> ForceMap
    forcedInTarget i (Bind _ (Pi _) rest) = forcedInTarget (i+1) (label i rest)
    forcedInTarget i t@(App f a) | (_, as) <- unApply t = unionMap guardedArgs as
    forcedInTarget _ _ = M.empty

    guardedArgs :: Term -> ForceMap
    guardedArgs t@(App f a) | (P (DCon _ _) _ _, args) <- unApply t
        = unionMap bareArg args `maxUnion` unionMap guardedArgs args
    guardedArgs t = bareArg t

    bareArg :: Term -> ForceMap
    bareArg (P _ (MN i ctor_arg) _) 
         | ctor_arg == txt "ctor_arg" = M.singleton i Unconditional
    bareArg  _                        = M.empty

    unionMap :: (a -> ForceMap) -> [a] -> ForceMap
    unionMap f = M.unionsWith max . map f

-- Calculate whether a collection of constructors is collapsible
-- and update the state accordingly.
collapseCons :: Name -> [(Name, Type)] -> Idris ()
collapseCons tn ctors = do
    ist <- getIState
    case ctors of
        _
          | all (ctorCollapsible ist) ctors
          , disjointTerms ctorTargetArgs
            -> mapM_ setCollapsible (tn : map fst ctors)

        [(cn, ct)]
            -> checkNewType ist cn ct

        _ -> return () -- nothing can be done
  where
    ctorTargetArgs = map (snd . unApply . getRetTy . snd) ctors

    ctorArity :: Type -> Int
    ctorArity = length . getArgTys

    ctorCollapsible :: IState -> (Name, Type) -> Bool
    ctorCollapsible ist (n, t) = all (`M.member` forceMap) [0 .. ctorArity t - 1]
      where
        forceMap = case lookupCtxt n (idris_optimisation ist) of
            oi:_ -> M.fromList $ forceable oi
            _    -> M.empty

    -- one constructor; if one remaining argument, treat as newtype
    checkNewType :: IState -> Name -> Type -> Idris ()
    checkNewType ist cn ct
        | oi:_ <- lookupCtxt cn opt
        , length (getArgTys ct) == 1 + forcedCnt (M.fromList $ forceable oi)
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
               [] -> do let oi = Optimise True False [] []
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
    applyOpts (x, y) = (,) <$> applyOpts x <*> applyOpts y
    stripCollapsed (x, y) = (,) <$> stripCollapsed x <*> stripCollapsed y

instance (Optimisable a, Optimisable b) => Optimisable (vs, a, b) where
    applyOpts (v, x, y) = (,,) v <$> applyOpts x <*> applyOpts y
    stripCollapsed (v, x, y) = (,,) v <$> stripCollapsed x <*> stripCollapsed y

instance Optimisable a => Optimisable [a] where
    applyOpts = mapM applyOpts
    stripCollapsed = mapM stripCollapsed

instance Optimisable a => Optimisable (Either a (a, a)) where
    applyOpts (Left  t) = Left  <$> applyOpts t
    applyOpts (Right t) = Right <$> applyOpts t
    stripCollapsed (Left  t) = Left  <$> stripCollapsed t
    stripCollapsed (Right t) = Right <$> stripCollapsed t

-- Raw is for compile time optimisation (before type checking)
-- Term is for run time optimisation (after type checking, collapsing allowed)

-- Compile time: no collapsing

instance Optimisable Raw where
    applyOpts t@(RApp f a)
        | (Var n, args) <- raw_unapply t -- MAGIC HERE
            = do args' <- mapM applyOpts args
                 i <- getIState
                 return $ case lookupCtxt n (idris_optimisation i) of
                    oi:_ -> applyDataOpt oi n args'
                    _    -> raw_apply (Var n) args'
        | otherwise = RApp <$> applyOpts f <*> applyOpts a

    applyOpts (RBind n b t) = RBind n <$> applyOpts b <*> applyOpts t
    applyOpts (RForce t)    = applyOpts t
    applyOpts t = return t

    stripCollapsed t = return t

-- Erase types (makes ibc smaller, and we don't need them)
instance Optimisable (Binder (TT Name)) where
    applyOpts (Let t v) = Let <$> return Erased <*> applyOpts v
    applyOpts b = return (b { binderTy = Erased })
    stripCollapsed (Let t v) = Let <$> return Erased <*> stripCollapsed v
    stripCollapsed b = return (b { binderTy = Erased })

instance Optimisable (Binder Raw) where
    applyOpts b = do t' <- applyOpts (binderTy b)
                     return (b { binderTy = t' })
    stripCollapsed (Let t v) = Let <$> stripCollapsed t <*> stripCollapsed v
    stripCollapsed b = do t' <- stripCollapsed (binderTy b)
                          return (b { binderTy = t' })

forcedArgSeq :: OptInfo -> [Maybe Forceability]
forcedArgSeq oi = map (\i -> M.lookup i forceMap) [0..]
  where
    forceMap = M.fromList $ forceable oi

forcedCnt :: ForceMap -> Int
forcedCnt = length . filter (== Unconditional) . M.elems

applyDataOpt :: OptInfo -> Name -> [Raw] -> Raw
applyDataOpt oi n args 
    = raw_apply (Var n) $ zipWith doForce (forcedArgSeq oi) args
  where
    doForce (Just Unconditional) a = RForce a
    doForce _ a = a

-- Run-time: do everything

prel = [txt "Nat", txt "Prelude"]

instance Optimisable (TT Name) where
    applyOpts (P _ (NS (UN fn) mod) _)
       | fn == txt "plus" && mod == prel
        = return (P Ref (sUN "prim__addBigInt") Erased)
    applyOpts (P _ (NS (UN fn) mod) _)
       | fn == txt "mult" && mod == prel
        = return (P Ref (sUN "prim__mulBigInt") Erased)
    applyOpts (App (P _ (NS (UN fn) mod) _) x)
       | fn == txt "fromIntegerNat" && mod == prel
        = applyOpts x
    applyOpts (P _ (NS (UN fn) mod) _)
       | fn == txt "fromIntegerNat" && mod == prel
        = return (App (P Ref (sNS (sUN "id") ["Basics","Prelude"]) Erased) Erased)
    applyOpts (P _ (NS (UN fn) mod) _)
       | fn == txt "toIntegerNat" && mod == prel
         = return (App (P Ref (sNS (sUN "id") ["Basics","Prelude"]) Erased) Erased)
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
    | length args == arity = doOpts n args (collapsible oi) (M.fromList $ forceable oi)
    | otherwise = let extra = satArgs (arity - length args)
                      tm = doOpts n (args ++ map (\n -> P Bound n Erased) extra)
                                    (collapsible oi) (M.fromList $ forceable oi) in
                      bind extra tm
  where
    satArgs n = map (\i -> sMN i "sat") [1..n]

    bind [] tm = tm
    bind (n:ns) tm = Bind n (Lam Erased) (pToV n (bind ns tm))

    -- Nat special cases
    -- TODO: Would be nice if this was configurable in idris source!
    doOpts (NS (UN z) [nat, prelude]) [] _ _ 
        | z == txt "Z" && nat == txt "Nat" && prelude == txt "Prelude"
          = Constant (BI 0)
    doOpts (NS (UN s) [nat, prelude]) [k] _ _
        | s == txt "S" && nat == txt "Nat" && prelude == txt "Prelude"
          = App (App (P Ref (sUN "prim__addBigInt") Erased) k) (Constant (BI 1))

    doOpts n args True _  = Erased
    doOpts n args _ forceMap
        | isnewtype oi = case args' of
            [val] -> val
            _     -> error $ "Can't happen (newtype not a singleton): " ++ show args'
        | otherwise = mkApp ctor' args'
      where
        ctor' = (P (DCon tag (arity - forcedCnt forceMap)) n Erased)
        args' = [t | (f, t) <- zip (forcedArgSeq oi) args, f /= Just Unconditional]

