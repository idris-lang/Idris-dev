{-# LANGUAGE CPP #-}
module Util.System(tempfile,environment) where

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

tempfile :: IO (FilePath, Handle)
tempfile = do env <- environment "TMPDIR"
              let dir = case env of
                              Nothing -> "/tmp"
                              (Just d) -> d
              openTempFile dir "esc"

environment :: String -> IO (Maybe String)
environment x = catchIO (do e <- getEnv x
                            return (Just e))
                      (\_ -> return Nothing)
