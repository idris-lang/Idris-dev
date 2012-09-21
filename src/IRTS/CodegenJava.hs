module IRTS.CodegenJava where

import IRTS.BCImp
import IRTS.Lang
import IRTS.Simplified
import Core.TT
import Paths_idris
import Util.System

import Data.Char
import System.Process
import System.Exit
import System.IO
import System.Directory
import Control.Monad

codegenJava :: [(Name, SDecl)] ->
               String -> -- output file name
               IO ()
codegenJava defs out = putStrLn "Not implemented yet"

