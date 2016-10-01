module Main where

import Idris.AbsSyntax
import Idris.Core.TT
import Idris.ElabDecls
import Idris.Main
import IRTS.CodegenC
import IRTS.Compiler

import Util.System

import Paths_idris

import Control.Monad
import System.Environment
import System.Exit



data Opts = Opts { inputs :: [FilePath],
                   interface :: Bool,
                   output :: FilePath }

showUsage = do putStrLn "A code generator which is intended to be called by the compiler, not by a user."
               putStrLn "Usage: idris-codegen-c <ibc-files> [-o <output-file>]"
               exitWith ExitSuccess

getOpts :: IO Opts
getOpts = do xs <- getArgs
             return $ process (Opts [] False "a.out") xs
  where
    process opts ("-o":o:xs) = process (opts { output = o }) xs
    process opts ("--interface":xs) = process (opts { interface = True }) xs
    process opts (x:xs) = process (opts { inputs = x:inputs opts }) xs
    process opts [] = opts

c_main :: Opts -> Idris ()
c_main opts = do runIO setupBundledCC
                 elabPrims
                 loadInputs (inputs opts) Nothing
                 mainProg <- if interface opts
                                then liftM Just elabMain
                                else return Nothing
                 ir <- compile (Via IBCFormat "c") (output opts) mainProg
                 runIO $ codegenC ir

main :: IO ()
main = do opts <- getOpts
          if (null (inputs opts))
             then showUsage
             else  runMain (c_main opts)
