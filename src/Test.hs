module Test where

import Parser
import Core
import Typecheck

test = do f <- readFile "test.mi"
          let Right defs = parseFile f
          print defs
          let ctxt = checkProgram [] defs
          print ctxt