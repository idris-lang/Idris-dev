{-# LANGUAGE DeriveDataTypeable #-}

module Idris.Error where

import Prelude hiding (catch)
import Idris.AbsSyntax
import Idris.Delaborate
import Idris.Output

import Idris.Core.TT
import Idris.Core.Typecheck
import Idris.Core.Constraints

import System.Console.Haskeline
import System.Console.Haskeline.MonadException
import Control.Monad.State.Strict
import Control.Monad.Error (throwError, catchError)
import System.IO.Error(isUserError, ioeGetErrorString)
import Data.Char
import Data.Typeable

iucheck :: Idris ()
iucheck = do tit <- typeInType
             when (not tit) $
                do ist <- getIState
                   (tclift $ ucheck (idris_constraints ist)) `idrisCatch`
                              (\e -> do setErrSpan (getErrSpan e)
                                        iputStrLn (pshow ist e))

showErr :: Err -> Idris String
showErr e = getIState >>= return . flip pshow e


report :: IOError -> String
report e
    | isUserError e = ioeGetErrorString e
    | otherwise     = show e

idrisCatch :: Idris a -> (Err -> Idris a) -> Idris a
idrisCatch = catchError


setAndReport :: Err -> Idris ()
setAndReport e = do ist <- getIState
                    let h = idris_outh ist
                    case (e) of
                      At fc e -> do setErrSpan fc
                                    ihWarn h fc $ pprintErr ist e
                      _ -> do setErrSpan (getErrSpan e)
                              ihWarn h emptyFC $ pprintErr ist e
  where unwrap (ProofSearchFail e) = e -- remove bookkeeping constructor
        unwrap e = e

ifail :: String -> Idris a
ifail = throwError . Msg

ierror :: Err -> Idris a
ierror = throwError

tclift :: TC a -> Idris a
tclift (OK v) = return v
tclift (Error err@(At fc e)) = do setErrSpan fc; throwError err
tclift (Error err) = throwError err

tctry :: TC a -> TC a -> Idris a
tctry tc1 tc2
    = case tc1 of
           OK v -> return v
           Error err -> tclift tc2

getErrSpan :: Err -> FC
getErrSpan (At fc _) = fc
getErrSpan _ = emptyFC
