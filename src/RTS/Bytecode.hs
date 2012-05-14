module RTS.Bytecode where

import Core.TT

data Value = VInt Int
           | VFloat Double
           | VString String
           | VChar Char
           | VBigInt Integer
           | VRef Int

data Bytecode = PUSH Value
              | SLIDE Int
              | DISCARD Int
              | DISCARDINT Int
              | DISCARDFLOAT Int
              | EVAL Bool
              | MKCON Tag Int
              | MKTHUNK Name Int Int
              | CALL Name
