module IRTS.CodegenCommon where

import Core.TT
import IRTS.Simplified

import Control.Exception
import System.Environment

data DbgLevel = NONE | DEBUG | TRACE deriving Eq
data OutputType = Raw | Object | Executable | MavenProject deriving (Eq, Show)

environment :: String -> IO (Maybe String)
environment x = Control.Exception.catch (do e <- getEnv x
                                            return (Just e))
                          (\y-> do return (y::SomeException);  return Nothing)
