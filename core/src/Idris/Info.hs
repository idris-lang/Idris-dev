{-|
Module      : Idris.Info
Description : Get information about Idris.
Copyright   : 2016 The Idris Community
License     : BSD3
Maintainer  : The Idris Community.
-}
module Idris.Info
  ( getIdrisDataDir
  , getIdrisLibDir
  , getIdrisDocDir
  , getIdrisFlagsLib
  , getIdrisFlagsInc
  , getIdrisFlagsEnv
  , getIdrisCC
  , getIdrisVersion
  , getIdrisVersionNoGit
  , getIdrisUserDataDir
  , getIdrisInitScript
  , getIdrisHistoryFile
  , getIdrisInstalledPackages
  , getIdrisLoggingCategories
  ) where

import Idris.AbsSyntax (loggingCatsStr)
import Idris.Imports (installedPackages)
import qualified IRTS.System as S

import Data.Version
import System.FilePath

getIdrisDataDir :: IO String
getIdrisDataDir = S.getIdrisDataDir

getIdrisDocDir :: IO String
getIdrisDocDir = S.getIdrisDocDir

getIdrisLibDir :: IO String
getIdrisLibDir = S.getIdrisLibDir

getIdrisFlagsLib :: IO [String]
getIdrisFlagsLib = S.getLibFlags

getIdrisFlagsInc :: IO [String]
getIdrisFlagsInc = S.getIncFlags

getIdrisFlagsEnv :: IO [String]
getIdrisFlagsEnv = S.getEnvFlags

getIdrisCC :: IO String
getIdrisCC = S.getCC

getIdrisVersion = showVersion S.version ++ suffix
  where
    suffix = if S.gitHash =="" then "" else "-" ++ S.gitHash

getIdrisVersionNoGit = S.version

getIdrisUserDataDir :: IO FilePath
getIdrisUserDataDir = S.getIdrisUserDataDir

getIdrisInitScript :: IO FilePath
getIdrisInitScript = S.getIdrisInitScript

getIdrisHistoryFile :: IO FilePath
getIdrisHistoryFile = S.getIdrisHistoryFile

getIdrisInstalledPackages :: IO [String]
getIdrisInstalledPackages = installedPackages

getIdrisLoggingCategories :: IO [String]
getIdrisLoggingCategories = return $ words loggingCatsStr
