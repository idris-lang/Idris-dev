{-|
Module      : IRTS.System
Description : Utilities for interacting with the System.
Copyright   :
License     : BSD3
Maintainer  : The Idris Community.
-}
{-# LANGUAGE CPP #-}
module IRTS.System( getIdrisDataFileByName
                  , getCC
                  , getLibFlags
                  , getIdrisDataDir
                  , getIdrisLibDir
                  , getIdrisDocDir
                  , getIdrisCRTSDir
                  , getIdrisJSRTSDir
                  , getIncFlags
                  , getEnvFlags
                  , version
                  , registerCodeGenerator
                  , getExtCodeGenerator
                  , registerIncFlag
                  , registerLibFlag
                  , registerInfoString
                  , getExtInfoStrings
                  ) where

#ifdef FREESTANDING
import Paths_idris (version)
import Target_idris
#else
import Paths_idris
#endif

import Control.Applicative ((<$>))
import Data.List.Split
import Data.Maybe (fromMaybe)
import Data.List (find, sortBy)
import Data.Function (on)
import System.Environment
import System.FilePath (addTrailingPathSeparator, (</>))

import Control.Concurrent.MVar
import System.IO.Unsafe

import IRTS.CodegenCommon (CodeGenerator)

type FlagPriority = Int

data IdrisExtensions = IdrisExtensions
  { codegens    :: [(String, CodeGenerator)]
  , incFlags    :: [(FlagPriority, String)]
  , libFlags    :: [(FlagPriority, String)]
  , infoStrings :: [(String, String)]
  }

idrisExt :: MVar IdrisExtensions
idrisExt = unsafePerformIO . newMVar $ IdrisExtensions [] [] [] []

registerCodeGenerator :: String -> CodeGenerator -> IO ()
registerCodeGenerator name cg = do
  env <- takeMVar idrisExt
  putMVar idrisExt $ env { codegens = (name, cg) : codegens env }

getExtCodeGenerator :: String -> IO (Maybe CodeGenerator)
getExtCodeGenerator name = do
  env <- readMVar idrisExt
  return . fmap snd . find ((== name) . fst) $ codegens env

registerIncFlag :: String -> FlagPriority -> IO ()
registerIncFlag flag pri = do
  env <- takeMVar idrisExt
  putMVar idrisExt $ env { incFlags = (pri, flag) : incFlags env }

registerLibFlag :: String -> FlagPriority -> IO ()
registerLibFlag flag pri = do
  env <- takeMVar idrisExt
  putMVar idrisExt $ env { libFlags = (pri, flag) : libFlags env }

getExtLibFlags :: IO [String]
getExtLibFlags = do env <- readMVar idrisExt
                    return . map snd . sortBy (compare `on` fst) $ libFlags env

getExtIncFlags :: IO [String]
getExtIncFlags = do env <- readMVar idrisExt
                    return . map snd . sortBy (compare `on` fst) $ incFlags env

registerInfoString :: String -> String -> IO ()
registerInfoString name val = do
  env <- takeMVar idrisExt
  putMVar idrisExt $ env { infoStrings = (name, val) : infoStrings env }

getExtInfoStrings :: IO [(String, String)]
getExtInfoStrings = do
  env <- readMVar idrisExt
  return $ infoStrings env

getIdrisDataDir :: IO String
getIdrisDataDir = do
  envValue <- lookupEnv "TARGET"
  case envValue of
    Nothing -> do
      ddir <- getDataDir
      return ddir
    Just ddir -> return ddir

getIdrisDataFileByName :: String -> IO FilePath
getIdrisDataFileByName fn = do
  dir <- getIdrisDataDir
  return $ dir </> fn

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

getCC :: IO String
getCC = fromMaybe "gcc" <$> lookupEnv "IDRIS_CC"

getEnvFlags :: IO [String]
getEnvFlags = maybe [] (splitOn " ") <$> lookupEnv "IDRIS_CFLAGS"


#if defined(freebsd_HOST_OS) || defined(dragonfly_HOST_OS)\
    || defined(openbsd_HOST_OS) || defined(netbsd_HOST_OS)
extraLib = ["-L/usr/local/lib"]
extraInclude = ["-I/usr/local/include"]
#else
extraLib = []
extraInclude = []
#endif

#ifdef IDRIS_GMP
gmpLib = ["-lgmp"]
#else
gmpLib = []
#endif

getLibFlags = do dir <- getIdrisCRTSDir
                 ext <- getExtLibFlags
                 return $ ["-L" ++ dir,
                           "-lidris_rts"] ++ ext ++ extraLib ++ gmpLib ++ ["-lpthread"]

getIdrisLibDir = addTrailingPathSeparator <$> overrideIdrisSubDirWith "libs" "IDRIS_LIBRARY_PATH"

getIdrisDocDir = addTrailingPathSeparator <$> overrideIdrisSubDirWith "docs" "IDRIS_DOC_PATH"

getIdrisJSRTSDir = do
  ddir <- getIdrisDataDir
  return $ addTrailingPathSeparator (ddir </> "jsrts")

getIdrisCRTSDir = do
  ddir <- getIdrisDataDir
  return $ addTrailingPathSeparator (ddir </> "rts")

getIncFlags = do dir <- getIdrisCRTSDir
                 ext <- getExtIncFlags
                 return $ ("-I" ++ dir) : ext ++ extraInclude
