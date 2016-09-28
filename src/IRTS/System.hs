{-|
Module      : IRTS.System
Description : Utilities for interacting with the System.
Copyright   :
License     : BSD3
Maintainer  : The Idris Community.
-}
{-# LANGUAGE CPP #-}
module IRTS.System( getDataFileName
                  , getDataDir
                  , getTargetDir
                  , getCC
                  , getLibFlags
                  , getIdrisLibDir
                  , getIdrisDocDir
                  , getIncFlags
                  , getEnvFlags
                  , version
                  ) where

import Data.List.Split

import Control.Applicative ((<$>))
import Data.Maybe (fromMaybe)
import System.FilePath ((</>), addTrailingPathSeparator)
import System.Environment

#ifdef FREESTANDING
import Target_idris
import Paths_idris (version)
#else
import Paths_idris
#endif

overrideIdrisDirWith :: String  -- ^ Sub directory in `getDataDir` location.
                     -> String  -- ^ Environment variable to get new location from.
                     -> IO FilePath
overrideIdrisDirWith fp envVar = do
  envValue <- lookupEnv envVar
  case envValue of
    Nothing -> do
      ddir <- getDataDir
      return (ddir </> fp)
    Just ddir -> return ddir

overrideIdrisLibDirWith :: String -> IO FilePath
overrideIdrisLibDirWith = overrideIdrisDirWith "libs"

overrideIdrisDocDirWith :: String -> IO FilePath
overrideIdrisDocDirWith = overrideIdrisDirWith "docs"

getCC :: IO String
getCC = fromMaybe "gcc" <$> lookupEnv "IDRIS_CC"

getEnvFlags :: IO [String]
getEnvFlags = maybe [] (splitOn " ") <$> lookupEnv "IDRIS_CFLAGS"

getTargetDir :: IO String
getTargetDir = overrideIdrisLibDirWith "TARGET"

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

getLibFlags = do dir <- getDataDir
                 return $ ["-L" ++ (dir </> "rts"),
                           "-lidris_rts"] ++ extraLib ++ gmpLib ++ ["-lpthread"]

getIdrisLibDir = addTrailingPathSeparator <$> overrideIdrisLibDirWith "IDRIS_LIBRARY_PATH"

getIdrisDocDir = addTrailingPathSeparator <$> overrideIdrisDocDirWith "IDRIS_DOC_PATH"


getIncFlags = do dir <- getDataDir
                 return $ ("-I" ++ dir </> "rts") : extraInclude
