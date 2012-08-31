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
          | LForeign FLang FType String [(FType, LExp)]
          | LOp PrimFn [LExp]
  deriving Show

data PrimFn = LPlus | LMinus | LTimes | LDiv | LEq | LLt | LLe | LGt | LGe
            | LFPlus | LFMinus | LFTimes | LFDiv | LFEq | LFLt | LFLe | LFGt | LFGe
            | LStrConcat | LStrLt | LStrEq | LStrLen
            | LIntFloat | LFloatInt | LIntStr | LStrInt | LFloatStr | LStrFloat
            | LPrintNum | LPrintStr | LReadStr
  deriving Show

-- Supported target languages for foreign calls

data FLang = LANG_C
  deriving Show

data FType = FInt | FString | FUnit | FPtr | FDouble | FAny
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

