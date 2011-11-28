{-# LANGUAGE FlexibleContexts #-}

module Core.Constraints(ucheck) where

import Core.TT

import Control.Applicative
import Control.Arrow
import Control.Monad.Error
import Control.Monad.RWS
import Control.Monad.State
import Data.List
import Data.Maybe
import qualified Data.Map as M


ucheck :: Int -> [(UConstraint, FC)] -> TC ()
ucheck num cs = case solve (mkNode num cs) of
                   Left _ -> tfail UniverseError
                   Right _ -> return ()

mkNode :: Int -> [(UConstraint, FC)] -> Node
mkNode num cs = relNode num (M.toList (mkRels cs M.empty))

type Relations = M.Map UExp [(UConstraint, FC)]

mkRels :: [(UConstraint, FC)] -> Relations -> Relations
mkRels [] acc = acc
mkRels ((c, f) : cs) acc 
    = case M.lookup (lhs c) acc of
            Nothing -> mkRels cs (M.insert (lhs c) [(c,f)] acc)
            Just rs -> mkRels cs (M.insert (lhs c) ((c,f):rs) acc)
  where lhs (ULT l _) = l
        lhs (ULE l _) = l

relNode :: Int -> [(UExp, [(UConstraint, FC)])] -> Node
relNode num [] = CI 0 $ map Le (map (expNode . UVar) [0..num])
relNode num ((c, cons) : cs) = relNode num cs

data Child = Lt Node | Le Node
  deriving Show

data Node = CI Int [Child]
          | CV String [Child]
  deriving Show

expNode :: UExp -> Node
expNode (UVar i) = CV (show (UVar i)) []
expNode (UVal i) = CI i []

test :: Node
test = CI 0 $ [Lt x, Lt y, Le z] ++ map Le ints
    where
        x = CV "x" []
        y = CV "y" [Lt z]
        z = CV "z" [Lt x]
        ints = [ -- CI 3 [Lt y]
               ]

add :: Node -> Node -> Node
add i node = undefined

test2 :: Node
test2 = CI 0 $ [ Le v84, Le q25 ] ++ map Le [g,e85,v29,f90,j45,g86,n45,v84,q25,y48,q45,h45,g90]
    where
        g   = CV "g"   [Le y48]
        e85 = CV "e85" [Le n45, Le q45, Le h45]
        v29 = CV "v29" [Lt g90]
        f90 = CV "f90" [Lt g90]
        j45 = CV "j45" [Lt f90]
        g86 = CV "g86" [Lt f90]
        n45 = CV "n45" []
        v84 = CV "v84" []
        q25 = CV "q25" []
        y48 = CV "y48" []
        q45 = CV "q45" []
        h45 = CV "h45" []
        g90 = CV "g90" []

cyclic :: Node
cyclic = CI 0 $ map Le [a,b,c]
    where
        a = CV "a" [Lt b]
        b = CV "b" [Lt c]
        c = CV "c" [Lt a]

-- onChild :: Int -> Child -> m ()
onChild i (Lt n) = solveFrom (i+1) n
onChild i (Le n) = solveFrom i n

solveFrom ::
    ( Applicative m
    , MonadState (M.Map String Int, [String]) m
    , MonadError String m
    ) => Int -> Node -> m ()
solveFrom num (CI i chs ) = do
    let numi = max num i
    mapM_ (onChild numi) chs
solveFrom num (CV nm chs) = do
    nms <- snd <$> get
    if nm `elem` nms
        then throwError $ "cycle: " ++ intercalate ", " nms
        else do
            modify $ second (nm:)                    -- add this node for cycle detection
            i <- M.lookup nm . fst <$> get
            let numi = max num (fromMaybe 0 i)
            modify $ first (M.insert nm numi)
            mapM_ (onChild numi) chs
            modify $ second (drop 1)                 -- remove the node

solve :: Node -> Either String (M.Map String Int)
solve n = fst <$> execStateT (solveFrom 0 n) (M.empty, [])
