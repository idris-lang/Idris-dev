{-# LANGUAGE CPP #-}
module Util.System(tempfile,environment,getCC,getLibFlags,getIdrisLibDir,getIncFlags) where

-- System helper functions.

import System.FilePath ((</>), addTrailingPathSeparator, normalise)
import System.Environment
import System.IO
#if MIN_VERSION_base(4,0,0)
import Control.Exception as CE
#endif

-- import Data.List
import Data.List.Split(splitOn)

import Paths_idris

#if MIN_VERSION_base(4,0,0)
catchIO :: IO a -> (IOError -> IO a) -> IO a
catchIO = CE.catch
#else
catchIO = catch
#endif

getCC :: IO String
getCC = do env <- environment "IDRIS_CC"
           case env of
                Nothing -> return "gcc"
                Just cc -> return cc

tempfile :: IO (FilePath, Handle)
tempfile = do env <- environment tempDirEnvVar
              let dir = case env of
                              Nothing -> "/tmp"
#ifdef mingw32_HOST_OS
                              -- ghc changes the path separators if we start program in a *nix shell
                              (Just d) -> normalise d
#else
                              (Just d) -> d
#endif
              openTempFile dir "idris"
#ifdef mingw32_HOST_OS
    where tempDirEnvVar = "TMP"
#else
    where tempDirEnvVar = "TMPDIR"
#endif

environment :: String -> IO (Maybe String)
environment x = catchIO (do e <- getEnv x
                            return (Just e))
                      (\_ -> return Nothing)

getLibFlags = do dir <- getDataDir
                 return $ "-L" ++ (dir </> "rts") ++ " -lidris_rts -lgmp -lpthread"

getIdrisLibDir = do dir <- getDataDir
                    return $ addTrailingPathSeparator dir

getIncFlags = do dir <- getDataDir
                 return $ "-I" ++ dir </> "rts"
