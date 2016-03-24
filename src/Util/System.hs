{-# LANGUAGE CPP, ForeignFunctionInterface #-}
module Util.System(tempfile,withTempdir,rmFile,catchIO, isWindows,
                   writeSource, writeSourceText, readSource,
                   setupBundledCC, isATTY) where
-- System helper functions.

import Control.Exception as CE
import Control.Monad (when)
import qualified Data.Text as T
import qualified Data.Text.IO as TIO

import Foreign.C

import System.Directory (getTemporaryDirectory
                        , removeFile
                        , removeDirectoryRecursive
                        , createDirectoryIfMissing
                        )
import System.FilePath ((</>), normalise)
import System.IO
import System.Info
import System.IO.Error

#ifdef FREESTANDING
import Tools_idris
import System.FilePath (isAbsolute, dropFileName)
import System.Directory (doesDirectoryExist)
import System.Environment (getEnv, setEnv, getExecutablePath)
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
            tty <- isATTYRaw 1 -- fd stdout
            return $ tty /= 0

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
                        let pathSep = if isWindows then ";" else ":"
                        present <- doesDirectoryExist target
                        when present
                            $ do newPath <- return $ target ++ pathSep ++ path
                                 setEnv "PATH" newPath
#else
setupBundledCC = return ()
#endif
