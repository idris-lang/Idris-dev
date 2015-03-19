-- | Check universe constraints.
module Idris.Core.Constraints(ucheck) where

import Idris.Core.TT hiding (I, Var)
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
ucheck = void . solve . filter (not . ignore)
    where ignore (c,_) = any (== Var (-1)) (varsIn c)
          -- TODO: remove the ignore when Idris.Core.Binary:598

newtype Var = Var Int
    deriving (Eq, Ord, Show)

type Domain = (Int, Int)

data SolverState =
    SolverState
        { queue       :: [(UConstraint, FC)]
        , domainStore :: M.Map Var ( Domain
                                   , [(UConstraint, FC)]      -- constraints that effected this variable
                                   )
        }

solve :: [(UConstraint, FC)] -> TC (M.Map Var Int)
solve inpConstraints = evalStateT (propagate >> extractSolution) initSolverState

    where

        initSolverState :: SolverState
        initSolverState = SolverState
            { queue = inpConstraints
            , domainStore = M.fromList
                [ (v, ((0, 10), []))
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

        -- propagate :: MonadState SolverState m => m ()
        propagate = do
            mcons <- nextConstraint
            case mcons of
                Nothing -> return ()
                Just (cons, fc) -> do
                    case cons of
                        ULE a b -> do
                            (lowerA, upperA) <- domainOf a
                            (lowerB, upperB) <- domainOf b
                            updateDomainOf (cons, fc) a (lowerA, min upperA upperB)
                            updateDomainOf (cons, fc) b (max lowerB lowerA, upperB)
                        ULT a b -> do
                            (lowerA, upperA) <- domainOf a
                            (lowerB, upperB) <- domainOf b
                            updateDomainOf (cons, fc) a (lowerA, min upperA (pred upperB))
                            updateDomainOf (cons, fc) b (max lowerB (succ lowerA), upperB)
                    propagate

        extractSolution :: (MonadState SolverState m, Functor m) => m (M.Map Var Int)
        extractSolution = M.map (fst . fst) <$> gets domainStore

        nextConstraint :: MonadState SolverState m => m (Maybe (UConstraint, FC))
        nextConstraint = do
            qu <- gets queue
            case qu of
                [] -> return Nothing
                (q:qs) -> do
                    modify $ \ st -> st { queue = qs \\ [q] }
                    return (Just q)

        domainOf :: MonadState SolverState m => UExp -> m (Int, Int)
        domainOf (UVar var) = gets (fst . (M.! Var var) . domainStore)
        domainOf (UVal val) = return (val, val)

        -- updateDomainOf :: MonadState SolverState m => UConstraint -> UExp -> (Int, Int) -> m ()
        updateDomainOf suspect (UVar var) dom = do
            doms <- gets domainStore
            let (oldDom, suspects) = doms M.! Var var
            let newDom = domainIntersect oldDom dom
            varsDoms <- mapM (\ (Var v) -> do
                                    d <- domainOf (UVar v)
                                    return (UVar v, d)
                             ) $ ordNub $ concatMap (varsIn . fst) (suspect : suspects)
            when (wipeOut newDom) $ lift $ Error $ Msg $ unlines
                $ "Universe inconsistency."
                : ("Working on: " ++ show (UVar var))
                : ("Old domain: " ++ show oldDom)
                : ("Inp domain: " ++ show dom)
                : ("New domain: " ++ show newDom)
                : "Involved constraints: "
                : map (("\t"++) . show) (suspect:suspects)
                ++ ["Involved variables: "]
                ++ map (\ (v,d) -> "\t"++ show v ++ " = " ++ show d) varsDoms
                -- ++ ["All constraints"]
                -- ++ map (show . fst) inpConstraints
            unless (oldDom == newDom) $ do
                modify $ \ st -> st { domainStore = M.insert (Var var) (newDom, suspect:suspects) doms }
                addToQueue (Var var)
        updateDomainOf _ UVal{} _ = return ()

        -- addToQueue :: MonadState SolverState m => Var -> m ()
        addToQueue var = do
            let cs = constraints M.! var
            modify $ \ st -> st { queue = queue st ++ ordNub cs }

        domainIntersect :: (Int, Int) -> (Int, Int) -> (Int, Int)
        domainIntersect (a,b) (c,d) = (max a c, min b d)

        wipeOut :: (Int, Int) -> Bool
        wipeOut (l, u) = l > u

ordNub :: Ord a => [a] -> [a]
ordNub = S.toList . S.fromList

varsIn :: UConstraint -> [Var]
varsIn (ULT a b) = [ Var v | UVar v <- [a,b] ]
varsIn (ULE a b) = [ Var v | UVar v <- [a,b] ]
