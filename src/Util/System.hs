module Util.System(tempfile,withTempdir,rmFile,catchIO, isWindows,
                   readSource, writeSource) where

-- System helper functions.
import Control.Monad (when)
import System.Directory (getTemporaryDirectory
                        , removeFile
                        , removeDirectoryRecursive
                        , createDirectoryIfMissing
                        )
import System.FilePath ((</>), normalise)
import System.IO
import System.Info
import System.IO.Error
import Control.Exception as CE

catchIO :: IO a -> (IOError -> IO a) -> IO a
catchIO = CE.catch

throwIO :: IOError -> IO a
throwIO = CE.throw

isWindows :: Bool
isWindows = os `elem` ["win32", "mingw32", "cygwin32"]

tempfile :: IO (FilePath, Handle)
tempfile = do dir <- getTemporaryDirectory
              openTempFile (normalise dir) "idris"

-- | Read a source file, same as readFile but make sure the encoding is utf-8.
readSource :: FilePath -> IO String
readSource f = do h <- openFile f ReadMode
                  hSetEncoding h utf8
                  hGetContents h

-- | Write a source file, same as writeFile except the encoding is set to utf-8
writeSource :: FilePath -> String -> IO ()
writeSource f s = withFile f WriteMode (\h -> hSetEncoding h utf8 >> hPutStr h s)

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

rmFile :: FilePath -> IO ()
rmFile f = do putStrLn $ "Removing " ++ f
              catchIO (removeFile f)
                      (\ioerr -> putStrLn $ "WARNING: Cannot remove file "
                                 ++ f ++ ", Error msg:" ++ show ioerr)
