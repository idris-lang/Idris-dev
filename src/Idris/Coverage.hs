module Idris.Coverage where

import Idris.AbsSyntax

-- Given a list of LHSs, generate a complete collection of clauses which cover all
-- cases. The ones which haven't been provided are marked 'absurd' so that the
-- checker will make sure they can't happen.

genClauses :: [PClause] -> [PClause]
genClauses xs = xs

