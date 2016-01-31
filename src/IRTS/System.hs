{-# LANGUAGE CPP #-}
module IRTS.System(getDataFileName, getDataDir, getTargetDir,getCC,getLibFlags,getIdrisLibDir,
                   getIncFlags, getEnvFlags, getMvn,getExecutablePom, version) where

import Util.System
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

getCC :: IO String
getCC = fromMaybe "gcc" <$> environment "IDRIS_CC"

getEnvFlags :: IO [String]
getEnvFlags = maybe [] (splitOn " ") <$> environment "IDRIS_CFLAGS"

mvnCommand :: String
#ifdef mingw32_HOST_OS
mvnCommand = "mvn.bat"
#else
mvnCommand = "mvn"
#endif

getMvn :: IO String
getMvn = fromMaybe mvnCommand <$> environment "IDRIS_MVN"

environment :: String -> IO (Maybe String)
environment = lookupEnv

getTargetDir :: IO String
getTargetDir = environment "TARGET" >>= maybe getDataDir return

#if defined(FREEBSD) || defined(DRAGONFLY)
extraLib = ["-L/usr/local/lib"]
#else
extraLib = []
#endif

#ifdef IDRIS_GMP
gmpLib = ["-lgmp"]
#else
gmpLib = []
#endif

getLibFlags = do dir <- getDataDir
                 return $ ["-L" ++ (dir </> "rts"),
                           "-lidris_rts"] ++ extraLib ++ gmpLib ++ ["-lpthread"]

getIdrisLibDir = do libPath <- environment "IDRIS_LIBRARY_PATH"
                    dir <- maybe getDataDir return libPath
                    return $ addTrailingPathSeparator dir

#if defined(FREEBSD) || defined(DRAGONFLY)
extraInclude = ["-I/usr/local/include"]
#else
extraInclude = []
#endif
getIncFlags = do dir <- getDataDir
                 return $ ("-I" ++ dir </> "rts") : extraInclude

getExecutablePom = do dir <- getDataDir
                      return $ dir </> "java" </> "executable_pom.xml"
