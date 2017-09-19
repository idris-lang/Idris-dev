module Main where

import Idris.AbsSyntax
import Idris.ElabDecls
import Idris.Main
import Idris.Options
import IRTS.CodegenJavaScript
import IRTS.Compiler

import Paths_idris

import Control.Monad

import System.Environment
import System.Exit

data Opts = Opts { inputs :: [FilePath]
                 , interface :: Bool
                 , output :: FilePath
                 }

showUsage = do putStrLn "A code generator which is intended to be called by the compiler, not by a user."
               putStrLn "Usage: idris-codegen-node <ibc-files> [-o <output-file>]"
               exitWith ExitSuccess

getOpts :: IO Opts
getOpts = do xs <- getArgs
             return $ process (Opts [] False "main.js") xs
  where
    process opts ("-o":o:xs) = process (opts { output = o }) xs
    process opts ("--interface":xs) = process (opts { interface = True }) xs
    process opts (x:xs) = process (opts { inputs = x:inputs opts }) xs
    process opts [] = opts

jsMain :: Opts -> Idris ()
jsMain opts = do elabPrims
                 loadInputs (inputs opts) Nothing
                 mainProg <- if interface opts
                                then return Nothing
                                else liftM Just elabMain
                 ir <- compile (Via IBCFormat "node") (output opts) mainProg
                 runIO $ codegenNode ir

main :: IO ()
main = do opts <- getOpts
          if (null (inputs opts))
             then showUsage
             else  runMain (jsMain opts)
