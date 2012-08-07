module IRTS.Lang where

import Core.TT

data LVar = Loc Int | Glob Name
  deriving Show

data LExp = LV LVar
          | LApp Bool Name [LExp] -- True = tail call
          | LLet Name LExp LExp -- name just for pretty printing
          | LCon Int Name [LExp]
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

addTags :: [(Name, LDecl)] -> [(Name, LDecl)]
addTags ds = tag 0 ds
  where tag i ((n, LConstructor n' t a) : as) 
            = (n, LConstructor n' i a) : tag (i + 1) as
        tag i (x : as) = x : tag i as
        tag i [] = []

