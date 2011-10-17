module Idris.Error where

import Idris.AbsSyntax
import Idris.Delaborate

import Core.TT
import Core.Typecheck

import Control.Monad.State
import System.IO.Error

report :: IOError -> String
report e
    | isUserError e = ioeGetErrorString e 
    | otherwise     = show e

-- Taken from the library source code - for ghc 6.12/7 compatibility
liftCatch :: (m (a,s) -> (e -> m (a,s)) -> m (a,s)) ->
    StateT s m a -> (e -> StateT s m a) -> StateT s m a
liftCatch catchError m h =
    StateT $ \s -> runStateT m s `catchError` \e -> runStateT (h e) s

idrisCatch :: Idris a -> (IOError -> Idris a) -> Idris a
idrisCatch op handler = liftCatch catch op handler

pshow :: IState -> Err -> String
pshow i (Msg s) = s
pshow i (CantUnify x y e) = "Can't unify " ++ show (delab i x)
                            ++ " with " ++ show (delab i y) 
                            -- ++ "\n\t(" ++ pshow i e ++ ")"

tclift :: Show a => TC a -> Idris a
tclift tc = case tc of
               OK v -> return v
               Error err -> do i <- get
                               fail (pshow i err)

