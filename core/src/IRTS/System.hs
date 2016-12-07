{-|
Module      : IRTS.System
Description : Utilities for interacting with the System.
Copyright   :
License     : BSD3
Maintainer  : The Idris Community.
-}

module IRTS.System( getDataFileName
                  , getCC
                  , getLibFlags
                  , getIdrisDataDir
                  , getIdrisLibDir
                  , getIdrisDocDir
                  , getIncFlags
                  , getEnvFlags
                  , version
                  , gitHash
                  , registerDataPaths
                  , registerCodeGenerator
                  , getCodeGenerator
                  , FlagPriority
                  , registerIncFlag
                  , registerLibFlag
                  , registerInfoString
                  , getInfoStrings
                  , getIdrisUserDataDir
                  , getIdrisInitScript
                  , getIdrisHistoryFile
                  ) where

import Paths_idris_core (version)
import Version_idris_core (gitHash)

import Control.Applicative ((<$>))
import Data.List.Split
import Data.Maybe (fromMaybe)
import Data.List (find, sortBy)
import Data.Function (on)
import System.Environment
import System.Directory (getAppUserDataDirectory)
import System.FilePath (addTrailingPathSeparator, (</>))

import Control.Concurrent.MVar
import System.IO.Unsafe

import IRTS.CodegenCommon (CodeGenerator)

type FlagPriority = Int

data IdrisEnvironment = IdrisEnvironment
  { dataDir           :: String
  , getDataFileNameFn :: FilePath -> IO FilePath
  , codegens          :: [(String, CodeGenerator)]
  , incFlags          :: [(FlagPriority, String)]
  , libFlags          :: [(FlagPriority, String)]
  , infoStrings       :: [(String, String)]
  }

undef = error "IRTS.System: Idris environment is uninitialized!"

idrisEnv :: MVar IdrisEnvironment
idrisEnv = unsafePerformIO . newMVar $
  IdrisEnvironment undef (const $ return undef) [] [] [] []

registerDataPaths :: String -> (FilePath -> IO FilePath) -> IO ()
registerDataPaths dd dfn = do
  env <- takeMVar idrisEnv
  putMVar idrisEnv $ env { dataDir = dd, getDataFileNameFn = dfn }

registerCodeGenerator :: String -> CodeGenerator -> IO ()
registerCodeGenerator name cg = do
  env <- takeMVar idrisEnv
  putMVar idrisEnv $ env { codegens = (name, cg) : codegens env }

getCodeGenerator :: String -> IO (Maybe CodeGenerator)
getCodeGenerator name = do
  env <- readMVar idrisEnv
  return . fmap snd . find ((== name) . fst) $ codegens env

registerIncFlag :: String -> FlagPriority -> IO ()
registerIncFlag flag pri = do
  env <- takeMVar idrisEnv
  putMVar idrisEnv $ env { incFlags = (pri, flag) : incFlags env }

registerLibFlag :: String -> FlagPriority -> IO ()
registerLibFlag flag pri = do
  env <- takeMVar idrisEnv
  putMVar idrisEnv $ env { libFlags = (pri, flag) : libFlags env }

getEnvFlags :: IO [String]
getEnvFlags = maybe [] (splitOn " ") <$> lookupEnv "IDRIS_CFLAGS"

getLibFlags :: IO [String]
getLibFlags = do env <- readMVar idrisEnv
                 return . map snd . sortBy (compare `on` fst) $ libFlags env

getIncFlags :: IO [String]
getIncFlags = do env <- readMVar idrisEnv
                 return . map snd . sortBy (compare `on` fst) $ incFlags env

getDataFileName :: FilePath -> IO FilePath
getDataFileName fp = do
  env <- readMVar idrisEnv
  getDataFileNameFn env fp

registerInfoString :: String -> String -> IO ()
registerInfoString name val = do
  env <- takeMVar idrisEnv
  putMVar idrisEnv $ env { infoStrings = (name, val) : infoStrings env }

getInfoStrings :: IO [(String, String)]
getInfoStrings = do
  env <- readMVar idrisEnv
  return $ infoStrings env

getIdrisDataDir :: IO String
getIdrisDataDir = do
  envValue <- lookupEnv "TARGET"
  case envValue of
    Nothing -> do
      env <- readMVar idrisEnv
      return $ dataDir env
    Just ddir -> return ddir

overrideIdrisSubDirWith :: String  -- ^ Sub directory in `getDataDir` location.
                        -> String  -- ^ Environment variable to get new location from.
                        -> IO FilePath
overrideIdrisSubDirWith fp envVar = do
  envValue <- lookupEnv envVar
  case envValue of
    Nothing -> do
      ddir <- getIdrisDataDir
      return (ddir </> fp)
    Just ddir -> return ddir

getIdrisLibDir :: IO FilePath
getIdrisLibDir = addTrailingPathSeparator <$> overrideIdrisSubDirWith "libs" "IDRIS_LIBRARY_PATH"

getIdrisDocDir :: IO FilePath
getIdrisDocDir = addTrailingPathSeparator <$> overrideIdrisSubDirWith "docs" "IDRIS_DOC_PATH"

getCC :: IO String
getCC = fromMaybe "gcc" <$> lookupEnv "IDRIS_CC"

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
