module Idris.Error where

import Idris.AbsSyntax
import Idris.Delaborate

import Core.TT
import Core.Typecheck

import Control.Monad.State
import System.IO.Error
import Data.Char

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

tclift :: Show a => TC a -> Idris a
tclift tc = case tc of
               OK v -> return v
               Error err -> do i <- get
                               case err of
                                  At (FC f l) e -> setErrLine l
                                  _ -> return ()
                               fail (pshow i err)

getErrLine str 
  = case span (/=':') str of
      (_, ':':rest) -> case span isDigit rest of
        (num, _) -> read num
      _ -> 0

