module Util.System(tempfile,withTempdir,rmFile,catchIO) where

-- System helper functions.
import Control.Monad (when)
import System.Directory (getTemporaryDirectory
                        , removeFile
                        , removeDirectoryRecursive
                        , createDirectoryIfMissing
                        )
import System.FilePath ((</>), normalise)
import System.IO
import System.IO.Error
import Control.Exception as CE

catchIO :: IO a -> (IOError -> IO a) -> IO a
catchIO = CE.catch

throwIO :: IOError -> IO a
throwIO = CE.throw

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

rmFile :: FilePath -> IO ()
rmFile f = do putStrLn $ "Removing " ++ f
              catchIO (removeFile f)
                      (\ioerr -> putStrLn $ "WARNING: Cannot remove file "
                                 ++ f ++ ", Error msg:" ++ show ioerr)
