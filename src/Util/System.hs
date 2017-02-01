{-|
Module      : Util.System
Description : Utilities for interacting with the system.
Copyright   :
License     : BSD3
Maintainer  : The Idris Community.
-}
{-# LANGUAGE CPP, ForeignFunctionInterface #-}
module Util.System( tempfile
                  , withTempdir
                  , rmFile
                  , catchIO
                  , isWindows
                  , writeSource
                  , writeSourceText
                  , readSource
                  , setupBundledCC
                  , isATTY
                  ) where

import Control.Exception as CE
import Control.Monad (when)
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import Foreign.C
import System.Directory (createDirectoryIfMissing, getTemporaryDirectory,
                         removeDirectoryRecursive, removeFile)
import System.FilePath (normalise, (</>))
import System.Info
import System.IO
import System.IO.Error

#ifdef FREESTANDING
import Data.List (intercalate)
import System.Directory (doesDirectoryExist)
import System.Environment (getEnv, getExecutablePath, setEnv)
import System.FilePath (dropFileName, isAbsolute, searchPathSeparator)
import Tools_idris
#endif

#ifdef mingw32_HOST_OS
import Graphics.Win32.Misc (getStdHandle, sTD_OUTPUT_HANDLE)
import System.Console.MinTTY (isMinTTYHandle)
#endif

catchIO :: IO a -> (IOError -> IO a) -> IO a
catchIO = CE.catch

isWindows :: Bool
isWindows = os `elem` ["win32", "mingw32", "cygwin32"]

-- | Create a temp file with the extensiom ext (in the format ".xxx")
tempfile :: String -> IO (FilePath, Handle)
tempfile ext = do dir <- getTemporaryDirectory
                  openTempFile (normalise dir) $ "idris" ++ ext

-- | Read a source file, same as readFile but make sure the encoding is utf-8.
readSource :: FilePath -> IO String
readSource f = do h <- openFile f ReadMode
                  hSetEncoding h utf8
                  hGetContents h

-- | Write a source file, same as writeFile except the encoding is set to utf-8
writeSource :: FilePath -> String -> IO ()
writeSource f s = withFile f WriteMode (\h -> hSetEncoding h utf8 >> hPutStr h s)

-- | Write a utf-8 source file from Text
writeSourceText :: FilePath -> T.Text -> IO ()
writeSourceText f s = withFile f WriteMode (\h -> hSetEncoding h utf8 >> TIO.hPutStr h s)

foreign import ccall "isatty" isATTYRaw :: CInt -> IO CInt

isATTY :: IO Bool
isATTY = do
            tty    <- isATTYRaw 1 -- fd stdout
            mintty <- isMinTTY
            return $ (tty /= 0) || mintty

-- | Return 'True' if the process's standard output is attached to a MinTTY
-- console (e.g., Cygwin or MSYS) on Windows. Return 'False' otherwise.
--
-- Unfortunately, we must check this separately since 'isATTY' always returns
-- 'False' on MinTTY consoles.
isMinTTY :: IO Bool
#ifdef mingw32_HOST_OS
isMinTTY = do
  h <- getStdHandle sTD_OUTPUT_HANDLE
  isMinTTYHandle h
#else
isMinTTY = return False
#endif

withTempdir :: String -> (FilePath -> IO a) -> IO a
withTempdir subdir callback
  = do dir <- getTemporaryDirectory
       let tmpDir = normalise dir </> subdir
       removeLater <- catchIO (createDirectoryIfMissing True tmpDir >> return True)
                              (\ ioError -> if isAlreadyExistsError ioError then return False
                                            else throw ioError
                              )
       result <- callback tmpDir
       when removeLater $ removeDirectoryRecursive tmpDir
       return result

rmFile :: FilePath -> IO ()
rmFile f = do
  result <- try (removeFile f)
  case result of
    Right _ -> putStrLn $ "Removed: " ++ f
    Left err -> handleExists err
     where handleExists e
            | isDoesNotExistError e = return ()
            | otherwise = putStrLn $ "WARNING: Cannot remove file "
                          ++ f ++ ", Error msg:" ++ show e

setupBundledCC :: IO()
#ifdef FREESTANDING
setupBundledCC = when hasBundledToolchain
                    $ do
                        exePath <- getExecutablePath
                        path <- getEnv "PATH"
                        tcDir <- return getToolchainDir
                        absolute <- return $ isAbsolute tcDir
                        target <- return $
                                    if absolute
                                       then tcDir
                                       else dropFileName exePath ++ tcDir
                        present <- doesDirectoryExist target
                        when present $ do
                          newPath <- return $ intercalate [searchPathSeparator] [target, path]
                          setEnv "PATH" newPath
#else
setupBundledCC = return ()
#endif
