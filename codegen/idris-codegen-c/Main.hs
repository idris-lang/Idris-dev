module Main where

import Idris.Core.TT
import Idris.AbsSyntax
import Idris.ElabDecls
import Idris.REPL

import IRTS.Compiler
import IRTS.CodegenC

import System.Environment
import System.Exit
import Control.Monad

import Paths_idris

import Util.System

data Opts = Opts { really :: Bool,
                   inputs :: [FilePath],
                   interface :: Bool,
                   output :: FilePath }

showUsage = do putStrLn "A code generator which is intended to be called by the compiler, not by a user.\n"
               putStrLn "Usage: idris-codegen-c --yes-really <ibc-files> [-o <output-file>]"
               exitWith ExitSuccess

getOpts :: IO Opts
getOpts = do xs <- getArgs
             return $ process (Opts False [] False "a.out") xs
  where
    process opts ("--yes-really":xs) = process (opts { really = True }) xs
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
                 ir <- compile (Via "c") (output opts) mainProg
                 runIO $ codegenC ir

main :: IO ()
main = do opts <- getOpts
          if (null (inputs opts))
             then showUsage
             else if (not $ really opts)
                     then do putStrLn "This code generator is intended to be called by the Idris compiler. \
                                      \Please pass Idris the '--codegen' flag to choose a backend."
                             exitWith ExitSuccess
                     else runMain (c_main opts)
