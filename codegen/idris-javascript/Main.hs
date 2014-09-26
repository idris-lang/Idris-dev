module Main where

import Idris.Core.TT
import Idris.AbsSyntax
import Idris.ElabDecls
import Idris.REPL

import IRTS.Compiler
import IRTS.CodegenJavaScript

import System.Environment
import System.Exit

import Paths_idris

data Opts = Opts { inputs :: [FilePath]
                 , output :: FilePath
                 }

showUsage = do putStrLn "Usage: idris-javascript <ibc-files> [-o <output-file>]"
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
                 ir <- compile (Via "javascript") (output opts) mainProg
                 runIO $ codegenJavaScript ir

main :: IO ()
main = do opts <- getOpts
          if (null (inputs opts))
             then showUsage
             else runMain (jsMain opts)
