{-# LANGUAGE PatternGuards #-}

module Idris.Transforms(transformPats, applyTransRules) where

import Idris.AbsSyntax
import Idris.Core.CaseTree
import Idris.Core.TT


transformPats :: IState -> [Either Term (Term, Term)] ->
                [Either Term (Term, Term)]
transformPats ist ps = map tClause ps where
  tClause (Left t) = Left t -- not a clause, leave it alone
  tClause (Right (lhs, rhs)) -- apply transforms on RHS
      = let rhs' = applyTransRules ist rhs in
            Right (lhs, rhs')

applyTransRules :: IState -> Term -> Term
applyTransRules ist tm = applyAll (idris_transforms ist) tm

applyAll :: Ctxt [(Term, Term)] -> Term -> Term
applyAll ts t = t 
