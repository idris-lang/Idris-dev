{-|
Module      : IRTS.BCImp
Description : Bytecode for a register/variable based VM (e.g. for generating code in an imperative language where we let the language deal with GC)
Copyright   :
License     : BSD3
Maintainer  : The Idris Community.
-}
module IRTS.BCImp where

import Idris.Core.TT
import IRTS.Lang
import IRTS.Simplified

data Reg = RVal | L Int

data BC = NOP

toBC :: (Name, SDecl) -> (Name, [BC])
toBC (n, SFun n' args locs exp)
   = (n, bc RVal exp)

bc :: Reg -> SExp -> [BC]
bc = undefined
