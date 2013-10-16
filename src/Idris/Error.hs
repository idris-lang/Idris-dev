{-# LANGUAGE DeriveDataTypeable #-}

module Idris.Error where

import Prelude hiding (catch)
import Idris.AbsSyntax
import Idris.Delaborate

import Core.TT
import Core.Typecheck
import Core.Constraints

import System.Console.Haskeline
import System.Console.Haskeline.MonadException
import Control.Monad.State
import Control.Monad.Error (throwError, catchError)
import System.IO.Error(isUserError, ioeGetErrorString)
import Data.Char
import Data.Typeable

iucheck :: Idris ()
iucheck = do tit <- typeInType
             when (not tit) $
                do ist <- getIState
                   (tclift $ ucheck (idris_constraints ist)) `idrisCatch`
                              (\e -> do setErrLine (getErrLine e)
                                        iputStrLn (pshow ist e))

showErr :: Err -> Idris String
showErr e = getIState >>= return . flip pshow e


report :: IOError -> String
report e
    | isUserError e = ioeGetErrorString e 
    | otherwise     = show e

--idrisCatch :: Idris a -> (SomeException -> Idris a) -> Idris a
--idrisCatch = catch

idrisCatch :: Idris a -> (Err -> Idris a) -> Idris a
idrisCatch = catchError


ifail :: String -> Idris a
ifail = throwError . Msg

ierror :: Err -> Idris a
ierror = throwError

tclift :: TC a -> Idris a
tclift (OK v) = return v
tclift (Error err@(At (FC f l) e)) = do setErrLine l ; throwError err
tclift (Error err) = throwError err

tctry :: TC a -> TC a -> Idris a
tctry tc1 tc2 
    = case tc1 of
           OK v -> return v
           Error err -> tclift tc2

getErrLine :: Err -> Int
getErrLine (At (FC _ l) _) = l
getErrLine _ = 0


