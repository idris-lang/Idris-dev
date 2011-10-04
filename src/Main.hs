module Main where

import System.Console.Readline

import Core.CoreParser
import Core.ShellParser
import Core.TT
import Core.Typecheck
import Core.ProofShell
import Core.Evaluate

import Idris.AbsSyntax
import Idris.Parser

main = do Just x <- readline "> "
          case parseExpr x of
              Left err -> print err
              Right d -> print d
          main

main'
     = do f <- readFile "test.mi"
          case parseFile f of
              Left err -> print err
              Right defs -> do
                print defs
                case checkProgram emptyContext defs of
                    OK ctxt -> do print (toAlist ctxt) 
                                  runShell (initState ctxt)
                                  return ()
                    err -> print err
