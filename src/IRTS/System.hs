{-# LANGUAGE CPP #-}
module IRTS.System(getTargetDir,getCC,getLibFlags,getIdrisLibDir,
                   getIncFlags,getMvn,getExecutablePom) where

import Util.System

import Control.Applicative ((<$>))
import Data.Maybe (fromMaybe)
import System.FilePath ((</>), addTrailingPathSeparator)
import System.Environment

import Paths_idris

getCC :: IO String
getCC = fromMaybe "gcc" <$> environment "IDRIS_CC"

mvnCommand :: String
#ifdef mingw32_HOST_OS
mvnCommand = "mvn.bat"
#else
mvnCommand = "mvn"
#endif

getMvn :: IO String
getMvn = fromMaybe mvnCommand <$> environment "IDRIS_MVN"

environment :: String -> IO (Maybe String)
environment x = catchIO (do e <- getEnv x
                            return (Just e))
                      (\_ -> return Nothing)

getTargetDir :: IO String
getTargetDir = environment "TARGET" >>= maybe getDataDir return

#if defined(FREEBSD) || defined(DRAGONFLY)
extraLib = " -L/usr/local/lib"
#else
extraLib = ""
#endif

#ifdef IDRIS_GMP
gmpLib = " -lgmp"
#else
gmpLib = ""
#endif

getLibFlags = do dir <- getDataDir
                 return $ "-L" ++ (dir </> "rts") ++
                          " -lidris_rts" ++ extraLib ++ gmpLib ++ " -lpthread"

getIdrisLibDir = do dir <- getDataDir
                    return $ addTrailingPathSeparator dir

#if defined(FREEBSD) || defined(DRAGONFLY)
extraInclude = " -I/usr/local/include"
#else
extraInclude = ""
#endif
getIncFlags = do dir <- getDataDir
                 return $ "-I" ++ dir </> "rts" ++ extraInclude

getExecutablePom = do dir <- getDataDir
                      return $ dir </> "java" </> "executable_pom.xml"
