module Idris.Providers where

import Core.TT
import Core.Evaluate
import Idris.AbsSyntax
import Idris.AbsSyntaxTree

-- | Wrap a type provider in the type of type providers
providerTy :: FC -> PTerm -> PTerm
providerTy fc tm = PApp fc (PRef fc $ UN "Provider") [PExp 0 False tm ""]

-- | Wrap the RHS of a type provider definition 
unProv :: FC -> PTerm -> PTerm
unProv fc tm = PApp fc (PRef fc $ NS (UN "unProv") ["Providers"]) [PExp 0 False tm ""]