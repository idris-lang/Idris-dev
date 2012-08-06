module IRTS.Lang where

import Core.TT

data LVar = Loc Int | Glob Name
  deriving Show

data LExp = LV LVar
          | LApp Name [LExp]
          | LLet LVar LExp LExp
          | LCon Int [LExp]
          | LCase LExp [LAlt]
          | LConst Const
          | LOp PrimFn [LExp]
  deriving Show

data PrimFn = LPlus | LMinus | LTimes | LDiv | LEq 
            | LPrintNum | LPrintStr
  deriving Show

data LAlt = LConCase Int Name [Name] LExp
          | LConstCase Const LExp
          | LDefaultCase LExp
  deriving Show

data LDecl = LFun Name [Name] LExp -- name, arg names, definition
           | LConstructor Name Int Int -- constructor name, tag, arity
  deriving Show

type LDefs = Ctxt LDecl

-- TODO: Add constructor tags, then scope and arity checker.

