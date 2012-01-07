module Idris.Error where

import Prelude hiding (catch)
import Idris.AbsSyntax
import Idris.Delaborate

import Core.TT
import Core.Typecheck
import Core.Constraints

import System.Console.Haskeline
import Control.Monad.State
import System.IO.Error(isUserError, ioeGetErrorString)
import Data.Char

iucheck :: Idris ()
iucheck = do tit <- typeInType
             when (not tit) $
                do ist <- get
                   idrisCatch (tclift $ ucheck (idris_constraints ist))
                              (\e -> do let msg = report e
                                        setErrLine (getErrLine msg)
                                        iputStrLn msg)

report :: IOError -> String
report e
    | isUserError e = ioeGetErrorString e 
    | otherwise     = show e

idrisCatch :: Idris a -> (IOError -> Idris a) -> Idris a
idrisCatch = catch

tclift :: TC a -> Idris a
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

