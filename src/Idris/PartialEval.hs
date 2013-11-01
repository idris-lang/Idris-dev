module Idris.PartialEval(partial_eval) where

import Idris.AbsSyntax

import Core.TT
import Core.Evaluate

import Debug.Trace

partial_eval :: Context -> [(Name, Maybe Int)] ->
                [Either Term (Term, Term)] ->
                [Either Term (Term, Term)]
partial_eval ctxt ns tms = map peClause tms where
   peClause (Left t) = Left t
   peClause (Right (lhs, rhs))
       = let rhs' = specialise ctxt [] (map toLimit ns) rhs in
             Right (lhs, rhs')

   toLimit (n, Nothing) = (n, 65536) -- somewhat arbitrary reduction limit
   toLimit (n, Just l) = (n, l)
