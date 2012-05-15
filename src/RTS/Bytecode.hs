module RTS.Bytecode where

import Core.TT
import RTS.SC

data Value = VInt Int
           | VFloat Double
           | VString String
           | VChar Char
           | VBigInt Integer
           | VRef Int
    deriving Show

data BCOp = PUSH Value
          | SLIDE Int
          | DISCARD Int
          | DISCARDINT Int
          | DISCARDFLOAT Int
          | EVAL Bool
          | MKCON Tag Arity
          | MKTHUNK Name Int Arity
          | MKUNIT
          | CASE [(Int, Bytecode)] (Maybe Bytecode)
          | SPLIT -- get arguments from constructor form
          | CALL Name
          | FOREIGNCALL String CType [CType] -- TT constants for types 
          | ERROR String
          | DUMP
    deriving Show

type Bytecode = [BCOp]

data BCProg = BCProg [(Name, Bytecode)]
    deriving Show

