{-# LANGUAGE CPP #-}
module Util.System(tempfile,withTempdir,getTargetDir,getCC,
                   getLibFlags,getIdrisLibDir,getIncFlags,rmFile,
                   getMvn,getExecutablePom,catchIO) where

-- System helper functions.
import Control.Monad (when)
import Control.Applicative ((<$>))
import Data.Maybe (fromMaybe)
import Distribution.Text (display)
import System.Directory (getTemporaryDirectory
                        , removeFile
                        , removeDirectoryRecursive
                        , createDirectoryIfMissing
                        )
import System.FilePath ((</>), addTrailingPathSeparator, normalise)
import System.Environment
import System.IO
import System.IO.Error
import Control.Exception as CE

import Paths_idris

catchIO :: IO a -> (IOError -> IO a) -> IO a
catchIO = CE.catch

throwIO :: IOError -> IO a
throwIO = CE.throw


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

tempfile :: IO (FilePath, Handle)
tempfile = do dir <- getTemporaryDirectory
              openTempFile (normalise dir) "idris"

withTempdir :: String -> (FilePath -> IO a) -> IO a
withTempdir subdir callback
  = do dir <- getTemporaryDirectory
       let tmpDir = (normalise dir) </> subdir
       removeLater <- catchIO (createDirectoryIfMissing True tmpDir >> return True)
                              (\ ioError -> if isAlreadyExistsError ioError then return False
                                            else throw ioError
                              )
       result <- callback tmpDir
       when removeLater $ removeDirectoryRecursive tmpDir
       return result

environment :: String -> IO (Maybe String)
environment x = catchIO (do e <- getEnv x
                            return (Just e))
                      (\_ -> return Nothing)

getTargetDir :: IO String
getTargetDir = environment "TARGET" >>= maybe getDataDir return

rmFile :: FilePath -> IO ()
rmFile f = do putStrLn $ "Removing " ++ f
              catchIO (removeFile f)
                      (\ioerr -> putStrLn $ "WARNING: Cannot remove file "
                                 ++ f ++ ", Error msg:" ++ show ioerr)

#ifdef FREEBSD
extraLib = " -L/usr/local/lib"
#else
extraLib = ""
#endif
getLibFlags = do dir <- getDataDir
                 return $ "-L" ++ (dir </> "rts") ++ " -lidris_rts" ++ extraLib ++ " -lgmp -lpthread"

getIdrisLibDir = do dir <- getDataDir
                    return $ addTrailingPathSeparator dir

#ifdef FREEBSD
extraInclude = " -I/usr/local/include"
#else
extraInclude = ""
#endif
getIncFlags = do dir <- getDataDir
                 return $ "-I" ++ dir </> "rts" ++ extraInclude

getExecutablePom = do dir <- getDataDir
                      return $ dir </> "java" </> "executable_pom.xml"
