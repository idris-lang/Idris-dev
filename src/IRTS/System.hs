{-# LANGUAGE CPP #-}
module IRTS.System(getDataFileName, getDataDir, getTargetDir,getCC,getLibFlags,getIdrisLibDir,
                   getIncFlags, getEnvFlags, version) where

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

overrideDataDirWith :: String -> IO FilePath
overrideDataDirWith envVar = do envValue <- lookupEnv envVar
                                maybe getDataDir return envValue

getCC :: IO String
getCC = fromMaybe "gcc" <$> lookupEnv "IDRIS_CC"

getEnvFlags :: IO [String]
getEnvFlags = maybe [] (splitOn " ") <$> lookupEnv "IDRIS_CFLAGS"

getTargetDir :: IO String
getTargetDir = overrideDataDirWith "TARGET"

#if defined(freebsd_HOST_OS) || defined(dragonfly_HOST_OS)
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

getIdrisLibDir = addTrailingPathSeparator <$> overrideDataDirWith "IDRIS_LIBRARY_PATH"

getIncFlags = do dir <- getDataDir
                 return $ ("-I" ++ dir </> "rts") : extraInclude
