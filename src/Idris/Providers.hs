module Idris.Providers where

import Core.TT
import Core.Evaluate
import Idris.AbsSyntax
import Idris.AbsSyntaxTree


providerTy :: FC -> PTerm -> PTerm
providerTy fc tm = PApp fc (PRef fc $ UN "Provider") [PExp 0 False tm ""]

unProv :: FC -> PTerm -> PTerm
unProv fc tm = PApp fc (PRef fc $ NS (UN "unProv") ["Providers"]) [PExp 0 False tm ""]