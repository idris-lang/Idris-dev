module Main where

import Idris.AbsSyntax
import Idris.Core.TT
import Idris.ElabDecls
import Idris.Main
import IRTS.CodegenJavaScript
import IRTS.Compiler

import Paths_idris

import System.Environment
import System.Exit

data Opts = Opts { inputs :: [FilePath]
                 , output :: FilePath
                 }

showUsage = do putStrLn "A code generator which is intended to be called by the compiler, not by a user."
               putStrLn "Usage: idris-codegen-node <ibc-files> [-o <output-file>]"
               exitWith ExitSuccess

getOpts :: IO Opts
getOpts = do xs <- getArgs
             return $ process (Opts [] "main.js") xs
  where
    process opts ("-o":o:xs) = process (opts { output = o }) xs
    process opts (x:xs) = process (opts { inputs = x:inputs opts }) xs
    process opts [] = opts

jsMain :: Opts -> Idris ()
jsMain opts = do elabPrims
                 loadInputs (inputs opts) Nothing
                 mainProg <- elabMain
                 ir <- compile (Via IBCFormat "node") (output opts) (Just mainProg)
                 runIO $ codegenNode ir

main :: IO ()
main = do opts <- getOpts
          if (null (inputs opts))
             then showUsage
             else  runMain (jsMain opts)
