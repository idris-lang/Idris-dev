module Main where

import CoreParser
import ShellParser
import Core
import Typecheck
import ProofState
import ProofShell

main = do f <- readFile "test.mi"
          let Right defs = parseFile f
          print defs
          let OK ctxt = checkProgram [] defs
          print ctxt
          runShell (initState ctxt)
