{-|
Module      : Idris.Info
Description : Get information about Idris.
Copyright   : 2016 The Idris Community
License     : BSD3
Maintainer  : The Idris Community.
-}
module Idris.Info
  ( getIdrisDataDir
  , getIdrisCRTSDir
  , getIdrisJSRTSDir
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
  , getIdrisDataFileByName
  ) where

import Idris.AbsSyntax (loggingCatsStr)
import Idris.Imports (installedPackages)
import qualified IRTS.System as S

import Paths_idris
import Version_idris (gitHash)

import Data.Version
import System.Directory
import System.FilePath

getIdrisDataDir :: IO String
getIdrisDataDir = S.getIdrisDataDir

getIdrisCRTSDir :: IO String
getIdrisCRTSDir = S.getIdrisCRTSDir

getIdrisJSRTSDir :: IO String
getIdrisJSRTSDir = S.getIdrisJSRTSDir

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
    suffix = if gitHash =="" then "" else "-" ++ gitHash

getIdrisVersionNoGit = S.version


-- | Get the platform-specific, user-specific Idris dir
getIdrisUserDataDir :: IO FilePath
getIdrisUserDataDir = getAppUserDataDirectory "idris"

-- | Locate the platform-specific location for the init script
getIdrisInitScript :: IO FilePath
getIdrisInitScript = do
  idrisDir <- getIdrisUserDataDir
  return $ idrisDir </> "repl" </> "init"

getIdrisHistoryFile :: IO FilePath
getIdrisHistoryFile = do
  udir <- getIdrisUserDataDir
  return (udir </> "repl" </> "history")

getIdrisInstalledPackages :: IO [String]
getIdrisInstalledPackages = installedPackages

getIdrisLoggingCategories :: IO [String]
getIdrisLoggingCategories = return $ words loggingCatsStr

getIdrisDataFileByName :: String -> IO FilePath
getIdrisDataFileByName = S.getIdrisDataFileByName
