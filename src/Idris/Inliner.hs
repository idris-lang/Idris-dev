module Idris.Inliner where

import Core.TT
import Idris.AbsSyntax

inlineDef :: IState -> [([Name], Term, Term)] -> [([Name], Term, Term)]
inlineDef ist d = d

-- Inlining is either top level (i.e. not in a function arg) or argument level

-- For each application in a term:
--    * Check if the function is inlinable
--        (Dictionaries are inlinable in an argument, not otherwise)
--      - If so, try inlining without reducing its arguments
--        + If successful, then continue on the result (top level)
--        + If not, reduce the arguments (argument level) and try again 
--      - If not, inline all the arguments (top level)
