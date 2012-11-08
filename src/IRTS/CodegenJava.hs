module IRTS.CodegenJava (codegenJava) where

import IRTS.BCImp
import IRTS.Lang
import IRTS.Simplified
import Core.TT
import Paths_idris
import Util.System
import IRTS.CodegenCommon

import Data.Char
import System.Process
import System.Exit
import System.IO
import System.Directory
import Control.Monad

codegenJava :: [(Name, SDecl)] ->
               String -> -- output file name
               OutputType ->
               IO ()
codegenJava defs out exec = putStrLn "Not implemented yet"

