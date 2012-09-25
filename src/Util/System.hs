{-# LANGUAGE CPP #-}
module Util.System(tempfile,environment,getCC) where

-- System helper functions.

import System.Environment
import System.IO
#if MIN_VERSION_base(4,0,0)
import Control.Exception as CE
#endif

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
tempfile = do env <- environment "TMPDIR"
              let dir = case env of
                              Nothing -> "/tmp"
                              (Just d) -> d
              openTempFile dir "idris"

environment :: String -> IO (Maybe String)
environment x = catchIO (do e <- getEnv x
                            return (Just e))
                      (\_ -> return Nothing)
