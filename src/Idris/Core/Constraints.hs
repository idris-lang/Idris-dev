-- | Check universe constraints.
module Idris.Core.Constraints(ucheck) where

import Idris.Core.TT hiding (I)
import Idris.Core.Typecheck

import Control.Applicative
import Control.Arrow
import Control.Monad.RWS
import Control.Monad.State
import qualified Data.Set as S
import Data.List
import Data.Maybe
import Data.Either
import qualified Data.Map.Strict as M

import Control.DeepSeq

import Debug.Trace

-- | Check that a list of universe constraints can be satisfied.
ucheck :: [(UConstraint, FC)] -> TC ()
ucheck = void . solve

-- TODO: change this to a newtype
type Var = Int

data SolverState =
    SolverState
        { queue       :: [(UConstraint, FC)]
        , domainStore :: M.Map Var (InfInt, InfInt)
        }

data InfInt = NegInf | I Int | PosInf
    deriving (Eq, Ord, Show)

instance Enum InfInt where
    succ (I x) = I (succ x)
    succ x = x
    pred (I x) = I (pred x)
    pred x = x
    toEnum = I
    fromEnum (I x) = x
    fromEnum NegInf = minBound
    fromEnum PosInf = maxBound


solve :: [(UConstraint, FC)] -> TC (M.Map Var Int)
solve inpConstraints = evalStateT (propagate >> extractSolution) initSolverState

    where

        initSolverState :: SolverState
        initSolverState = SolverState
            { queue = inpConstraints
            , domainStore = M.fromList
                [ (v, (I 0, I 10))
                | v <- ordNub [ v
                              | (c, _) <- inpConstraints
                              , v <- varsIn c
                              ]
                ]
            }

        constraints :: M.Map Var [(UConstraint, FC)]
        constraints = M.fromListWith (++)
            [ (v, [(c,fc)])
            | (c, fc) <- inpConstraints
            , v <- varsIn c
            ]

        varsIn :: UConstraint -> [Var]
        varsIn (ULT a b) = [ v | UVar v <- [a,b] ]
        varsIn (ULE a b) = [ v | UVar v <- [a,b] ]

        -- propagate :: MonadState SolverState m => m ()
        propagate = do
            mcons <- nextConstraint
            case mcons of
                Nothing -> return ()
                Just (cons, _fc) -> do
                    case cons of
                        ULE a b -> do
                            (lowerA, upperA) <- domainOf a
                            (lowerB, upperB) <- domainOf b
                            updateDomainOf a (lowerA, min upperA upperB)
                            updateDomainOf b (max lowerB lowerA, upperB)
                        ULT a b -> do
                            (lowerA, upperA) <- domainOf a
                            (lowerB, upperB) <- domainOf b
                            updateDomainOf a (lowerA, min upperA (pred upperB))
                            updateDomainOf b (max lowerB (succ lowerA), upperB)
                    propagate

        extractSolution :: (MonadState SolverState m, Functor m) => m (M.Map Var Int)
        extractSolution = M.map extractVal <$> gets domainStore

        extractVal :: (InfInt, InfInt) -> Int
        extractVal (_, I x) = x
        extractVal (I x, _) = x
        extractVal _ = 0

        nextConstraint :: MonadState SolverState m => m (Maybe (UConstraint, FC))
        nextConstraint = do
            qu <- gets queue
            case qu of
                [] -> return Nothing
                (q:qs) -> do
                    modify $ \ st -> st { queue = qs \\ [q] }
                    return (Just q)

        domainOf :: MonadState SolverState m => UExp -> m (InfInt, InfInt)
        domainOf (UVar var) = gets ((M.! var) . domainStore)
        domainOf (UVal val) = return (I val, I val)

        -- updateDomainOf :: MonadState SolverState m => UExp -> (InfInt, InfInt) -> m ()
        updateDomainOf (UVar var) dom = do
            doms <- gets domainStore
            let oldDom = doms M.! var
            let newDom = domainIntersect oldDom dom
            when (wipeOut newDom) $ lift $ Error UniverseError
            unless (oldDom == newDom) $ do
                modify $ \ st -> st { domainStore = M.insert var newDom doms }
                addToQueue var
        updateDomainOf UVal{} _ = return ()

        -- addToQueue :: MonadState SolverState m => Var -> m ()
        addToQueue var = do
            let cs = constraints M.! var
            modify $ \ st -> st { queue = queue st ++ ordNub cs }

        domainIntersect :: (InfInt, InfInt) -> (InfInt, InfInt) -> (InfInt, InfInt)
        domainIntersect (a,b) (c,d) = (max a c, min b d)

        wipeOut :: (InfInt, InfInt) -> Bool
        wipeOut (l, u) = l > u

ordNub :: Ord a => [a] -> [a]
ordNub = S.toList . S.fromList
