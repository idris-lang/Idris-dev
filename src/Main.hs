module Main where

import CoreParser
import ShellParser
import Core
import Typecheck
import ProofShell

main = do f <- readFile "test.mi"
          let Right defs = parseFile f
          print defs
          case checkProgram [] defs of
             OK ctxt -> do print ctxt 
                           runShell (initState ctxt)
                           return ()
             err -> print err
