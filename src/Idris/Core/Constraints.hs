-- | Check universe constraints.
module Idris.Core.Constraints ( ucheck ) where

import Idris.Core.TT ( TC(..), UExp(..), UConstraint(..), FC(..), 
                       ConstraintFC(..), Err'(..) )

import Control.Applicative
import Control.Monad.State.Strict
import Data.List ( partition )
import qualified Data.Map.Strict as M
import qualified Data.Set as S


-- | Check that a list of universe constraints can be satisfied.
ucheck :: S.Set ConstraintFC -> TC ()
ucheck = void . solve 10 . S.filter (not . ignore)
    where
        -- TODO: remove the first ignore clause once Idris.Core.Binary:598 is dealt with
        ignore (ConstraintFC c _) | any (== Var (-1)) (varsIn c) = True
        ignore (ConstraintFC (ULE a b) _) = a == b
        ignore _ = False

newtype Var = Var Int
    deriving (Eq, Ord, Show)

data Domain = Domain Int Int
    deriving (Eq, Ord, Show)

data SolverState =
    SolverState
        { queue       :: Queue
        , domainStore :: M.Map Var ( Domain
                                   , S.Set ConstraintFC        -- constraints that effected this variable
                                   )
        , cons_lhs    :: M.Map Var (S.Set ConstraintFC)
        , cons_rhs    :: M.Map Var (S.Set ConstraintFC)
        }

data Queue = Queue [ConstraintFC] (S.Set UConstraint)


solve :: Int -> S.Set ConstraintFC -> TC (M.Map Var Int)
solve maxUniverseLevel ucs =
    evalStateT (propagate >> extractSolution) initSolverState

    where
        inpConstraints = S.toAscList ucs

        -- | initial solver state.
        --   the queue contains all constraints, the domain store contains the initial domains.
        initSolverState :: SolverState
        initSolverState =
            let
                (initUnaryQueue, initQueue) = partition (\ c -> length (varsIn (uconstraint c)) == 1) inpConstraints
            in
                SolverState
                    { queue = Queue (initUnaryQueue ++ initQueue) (S.fromList (map uconstraint (initUnaryQueue ++ initQueue)))
                    , domainStore = M.fromList
                        [ (v, (Domain 0 maxUniverseLevel, S.empty))
                        | v <- ordNub [ v
                                      | ConstraintFC c _ <- inpConstraints
                                      , v <- varsIn c
                                      ]
                        ]
                    , cons_lhs = constraintsLHS
                    , cons_rhs = constraintsRHS
                    }

        lhs (ULT (UVar x) _) = Just (Var x)
        lhs (ULE (UVar x) _) = Just (Var x)
        lhs _ = Nothing

        rhs (ULT _ (UVar x)) = Just (Var x)
        rhs (ULE _ (UVar x)) = Just (Var x)
        rhs _ = Nothing

        -- | a map from variables to the list of constraints the variable occurs in. (in the LHS of a constraint)
        constraintsLHS :: M.Map Var (S.Set ConstraintFC)
        constraintsLHS = M.fromListWith S.union
            [ (v, S.singleton (ConstraintFC c fc))
            | (ConstraintFC c fc) <- inpConstraints
            , let vars = varsIn c
            , length vars > 1               -- do not register unary constraints
            , v <- vars
            , lhs c == Just v
            ]

        -- | a map from variables to the list of constraints the variable occurs in. (in the RHS of a constraint)
        constraintsRHS :: M.Map Var (S.Set ConstraintFC)
        constraintsRHS = M.fromListWith S.union
            [ (v, S.singleton (ConstraintFC c fc))
            | (ConstraintFC c fc) <- inpConstraints
            , let vars = varsIn c
            , length vars > 1               -- do not register unary constraints
            , v <- vars
            , rhs c == Just v
            ]

        -- | this is where the actual work is done.
        --   dequeue the first constraint,
        --   filter domains,
        --   update domains (possibly resulting in a domain wipe out),
        --   until the queue is empty.
        propagate :: StateT SolverState TC ()
        propagate = do
            mcons <- nextConstraint
            case mcons of
                Nothing -> return ()
                Just (ConstraintFC cons fc) -> do
                    case cons of
                        ULE a b -> do
                            Domain lowerA upperA <- domainOf a
                            Domain lowerB upperB <- domainOf b
                            when (upperB < upperA) $ updateUpperBoundOf (ConstraintFC cons fc) a upperB
                            when (lowerA > lowerB) $ updateLowerBoundOf (ConstraintFC cons fc) b lowerA
                        ULT a b -> do
                            Domain lowerA upperA <- domainOf a
                            Domain lowerB upperB <- domainOf b
                            let upperB_pred = pred upperB
                            let lowerA_succ = succ lowerA
                            when (upperB_pred < upperA) $ updateUpperBoundOf (ConstraintFC cons fc) a upperB_pred
                            when (lowerA_succ > lowerB) $ updateLowerBoundOf (ConstraintFC cons fc) b lowerA_succ
                    propagate

        -- | extract a solution from the state.
        extractSolution :: (MonadState SolverState m, Functor m) => m (M.Map Var Int)
        extractSolution = M.map (extractValue . fst) <$> gets domainStore

        extractValue :: Domain -> Int
        extractValue (Domain x _) = x

        -- | dequeue the first constraint.
        nextConstraint :: MonadState SolverState m => m (Maybe ConstraintFC)
        nextConstraint = do
            Queue list set <- gets queue
            case list of
                [] -> return Nothing
                (q:qs) -> do
                    modify $ \ st -> st { queue = Queue qs (S.delete (uconstraint q) set) }
                    return (Just q)

        -- | look up the domain of a variable from the state.
        --   for convenience, this function also accepts UVal's and returns a singleton domain for them.
        domainOf :: MonadState SolverState m => UExp -> m Domain
        domainOf (UVar var) = gets (fst . (M.! Var var) . domainStore)
        domainOf (UVal val) = return (Domain val val)

        asPair :: Domain -> (Int, Int)
        asPair (Domain x y) = (x, y)

        updateUpperBoundOf :: ConstraintFC -> UExp -> Int -> StateT SolverState TC ()
        updateUpperBoundOf suspect (UVar var) upper = do
            doms <- gets domainStore
            let (oldDom@(Domain lower _), suspects) = doms M.! Var var
            let newDom = Domain lower upper
            when (wipeOut newDom) $
              lift $ Error $
                UniverseError (ufc suspect) (UVar var)
                              (asPair oldDom) (asPair newDom)
                              (suspect : S.toList suspects)
            modify $ \ st -> st { domainStore = M.insert (Var var) (newDom, S.insert suspect suspects) doms }
            addToQueueRHS (uconstraint suspect) (Var var)
        updateUpperBoundOf _ UVal{} _ = return ()

        updateLowerBoundOf :: ConstraintFC -> UExp -> Int -> StateT SolverState TC ()
        updateLowerBoundOf suspect (UVar var) lower = do
            doms <- gets domainStore
            let (oldDom@(Domain _ upper), suspects) = doms M.! Var var
            let newDom = Domain lower upper
            when (wipeOut newDom) $ lift $ Error $ At (ufc suspect) $ Msg $ unlines
                $ "Universe inconsistency."
                : ("Working on: " ++ show (UVar var))
                : ("Old domain: " ++ show oldDom)
                : ("New domain: " ++ show newDom)
                : "Involved constraints: "
                : map (("\t"++) . show) (suspect : S.toList suspects)
            modify $ \ st -> st { domainStore = M.insert (Var var) (newDom, S.insert suspect suspects) doms }
            addToQueueLHS (uconstraint suspect) (Var var)
        updateLowerBoundOf _ UVal{} _ = return ()

        -- | add all constraints (with the given var on the lhs) to the queue
        addToQueueLHS :: MonadState SolverState m => UConstraint -> Var -> m ()
        addToQueueLHS thisCons var = do
            clhs <- gets cons_lhs
            case M.lookup var clhs of
                Nothing -> return ()
                Just cs -> do
                    Queue list set <- gets queue
                    let set' = S.insert thisCons set
                    let newCons = [ c | c <- S.toList cs, uconstraint c `S.notMember` set' ]
                    if null newCons
                        then return ()
                        else modify $ \ st -> st { queue = Queue (list ++ newCons)
                                                                 (S.union set (S.fromList (map uconstraint newCons))) }

        -- | add all constraints (with the given var on the rhs) to the queue
        addToQueueRHS :: MonadState SolverState m => UConstraint -> Var -> m ()
        addToQueueRHS thisCons var = do
            crhs <- gets cons_rhs
            case M.lookup var crhs of
                Nothing -> return ()
                Just cs -> do
                    Queue list set <- gets queue
                    let set' = S.insert thisCons set
                    let newCons = [ c | c <- S.toList cs, uconstraint c `S.notMember` set' ]
                    if null newCons
                        then return ()
                        else modify $ \ st -> st { queue = Queue (list ++ newCons)
                                                                 (insertAll (map uconstraint newCons) set) }

        insertAll [] s = s
        insertAll (x : xs) s = insertAll xs (S.insert x s)

        -- | check if a domain is wiped out.
        wipeOut :: Domain -> Bool
        wipeOut (Domain l u) = l > u

ordNub :: Ord a => [a] -> [a]
ordNub = S.toList . S.fromList

-- | variables in a constraint
varsIn :: UConstraint -> [Var]
varsIn (ULT a b) = [ Var v | UVar v <- [a,b] ]
varsIn (ULE a b) = [ Var v | UVar v <- [a,b] ]
