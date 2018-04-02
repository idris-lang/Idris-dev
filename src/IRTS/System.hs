{-|
Module      : IRTS.System
Description : Utilities for interacting with the System.

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
                  ) where

#ifdef FREESTANDING
import Paths_idris (version)
import Target_idris
#else
import Paths_idris
#endif
import BuildFlags_idris

import Control.Applicative ((<$>))
import Data.List.Split
import Data.Maybe (fromMaybe)
import System.Environment
import System.FilePath (addTrailingPathSeparator, dropTrailingPathSeparator,
                        (</>))


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
getCC = fromMaybe cc <$> lookupEnv "IDRIS_CC"
  where
#ifdef mingw32_HOST_OS
    cc = "gcc"
#else
    cc = "cc"
#endif

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

extraLibFlags = map ("-L" ++) extraLibDirs

getLibFlags = do dir <- getIdrisCRTSDir
                 return $ extraLibFlags
                   ++ extraLib
                   ++ ["-L" ++ dropTrailingPathSeparator dir, "-lidris_rts"]
                   ++ gmpLib
                   ++ ["-lpthread"]

getIdrisLibDir = addTrailingPathSeparator <$> overrideIdrisSubDirWith "libs" "IDRIS_LIBRARY_PATH"

getIdrisDocDir = addTrailingPathSeparator <$> overrideIdrisSubDirWith "docs" "IDRIS_DOC_PATH"

getIdrisJSRTSDir = do
  ddir <- getIdrisDataDir
  return $ addTrailingPathSeparator (ddir </> "jsrts")

getIdrisCRTSDir = do
  ddir <- getIdrisDataDir
  return $ addTrailingPathSeparator (ddir </> "rts")

getIncFlags = do dir <- getIdrisCRTSDir
                 return $ ("-I" ++ dropTrailingPathSeparator dir) : extraInclude
