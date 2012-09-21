module IRTS.BCImp where

-- Bytecode for a register/variable based VM (e.g. for generating code in an 
-- imperative language where we let the language deal with GC)

import IRTS.Lang
import IRTS.Simplified
import Core.TT

data Reg = RVal | L Int

data BC = NOP

toBC :: (Name, SDecl) -> (Name, [BC])
toBC (n, SFun n' args locs exp)
   = (n, bc RVal exp)

bc :: Reg -> SExp -> [BC]
bc = undefined
