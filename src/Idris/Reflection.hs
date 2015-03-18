{-|
Handy tools for doing reflection.
-}
module Idris.Reflection where

import Idris.Core.TT
import Idris.AbsSyntaxTree (PArg'(..), PArg, PTerm(Placeholder))

data RArg = RExplicit { argName :: Name, argTy :: Raw }
          | RImplicit { argName :: Name, argTy :: Raw }
          | RConstraint { argName :: Name, argTy :: Raw }

data RTyDecl = RDeclare Name [RArg] Raw

rArgToPArg :: RArg -> PArg
rArgToPArg (RExplicit n _) = PExp 0 [] n Placeholder
rArgToPArg (RImplicit n _) = PImp 0 False [] n Placeholder
rArgToPArg (RConstraint n _) = PConstraint 0 [] n Placeholder
