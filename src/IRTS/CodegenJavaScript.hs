{-# LANGUAGE PatternGuards #-}

module IRTS.CodegenJavaScript (codegenJavaScript) where

import Idris.AbsSyntax
import IRTS.Bytecode
import IRTS.Lang
import IRTS.Simplified
import IRTS.CodegenCommon
import Core.TT
import Paths_idris
import Util.System

import Control.Arrow
import Data.Char
import Data.List
import System.IO

type NamespaceName = String

idrNamespace :: NamespaceName
idrNamespace = "__IDR__"

codegenJavaScript
  :: [(Name, SDecl)]
  -> FilePath
  -> OutputType
  -> IO ()
codegenJavaScript definitions filename outputType =
  writeFile filename output
  where
    def = map (first translateNamespace) definitions

    mainLoop :: String
    mainLoop = intercalate "\n" [ "\nfunction main() {"
                                , createTailcall "__IDR__.runMain0()"
                                , "}\n\nmain();\n"
                                ]

    output :: String
    output = concat [ idrRuntime
                    , concatMap (translateModule Nothing) def
                    , mainLoop
                    ]

idrRuntime :: String
idrRuntime =
  createModule Nothing idrNamespace $ concat
    [ "__IDR__.IntType = { type: 'IntType' };"

    , "__IDR__.Tailcall = function(f) { this.f = f };"

    , "__IDR__.Con = function(i,name,vars)"
    , "{this.i = i;this.name = name;this.vars =  vars;};\n"

    ,    "__IDR__.tailcall = function(f){\n"
      ++ "var __f = f;\n"
      ++ "while (__f) {\n"
      ++ "var f = __f;\n"
      ++ "__f = null;\n"
      ++ "var ret = f();\n"
      ++ "if (ret instanceof __IDR__.Tailcall) {\n"
      ++ "__f = ret.f;"
      ++ "\n} else {\n"
      ++ "return ret;"
      ++ "\n}"
      ++ "\n}"
      ++ "\n};\n"

    , "var newline_regex =/(.*)\\n$/;\n"

    ,    "__IDR__.print = function(s){\n"
      ++ "var m = s.match(newline_regex);\n"
      ++ "console.log(m ? m[1] : s);"
      ++ "\n};\n"
    ]

createModule :: Maybe String -> NamespaceName -> String -> String
createModule toplevel modname body =
  concat [header modname, body, footer modname]
  where
    header :: NamespaceName -> String
    header modname =
      concatMap (++ "\n")
        [ "\nvar " ++ modname ++ ";"
        , "(function(" ++ modname ++ "){"
        ]

    footer :: NamespaceName -> String
    footer modname =
      let m = maybe "" (++ ".") toplevel ++ modname in
         "\n})("
      ++ m
      ++ " || ("
      ++ m
      ++ " = {})"
      ++ ");\n"

translateModule :: Maybe String -> ([String], SDecl) -> String
translateModule toplevel ([modname], decl) =
  let body = translateDeclaration modname decl in
      createModule toplevel modname body
translateModule toplevel (n:ns, decl) =
  createModule toplevel n $ translateModule (Just n) (ns, decl)

translateIdentifier :: String -> String
translateIdentifier =
  concatMap replaceBadChars
  where replaceBadChars :: Char -> String
        replaceBadChars ' '  = "_"
        replaceBadChars '@'  = "__at__"
        replaceBadChars '['  = "__OSB__"
        replaceBadChars ']'  = "__CSB__"
        replaceBadChars '('  = "__OP__"
        replaceBadChars ')'  = "__CP__"
        replaceBadChars '{'  = "__OB__"
        replaceBadChars '}'  = "__CB__"
        replaceBadChars '!'  = "__bang__"
        replaceBadChars '#'  = "__hash__"
        replaceBadChars '.'  = "__dot__"
        replaceBadChars ':'  = "__colon__"
        replaceBadChars '+'  = "__plus__"
        replaceBadChars '-'  = "__minus__"
        replaceBadChars '<'  = "__lt__"
        replaceBadChars '>'  = "__gt__"
        replaceBadChars '='  = "__eq__"
        replaceBadChars '|'  = "__pipe__"
        replaceBadChars '\'' = "__apo__"
        replaceBadChars c
          | isDigit c = "__" ++ [c] ++ "__"
          | otherwise = [c]

translateNamespace :: Name -> [String]
translateNamespace (UN _)    = [idrNamespace]
translateNamespace (NS _ ns) = map translateIdentifier ns
translateNamespace (MN _ _)  = [idrNamespace]

translateName :: Name -> String
translateName (UN name)   = translateIdentifier name
translateName (NS name _) = translateName name
translateName (MN i name) = translateIdentifier name ++ show i

translateQualifiedName :: Name -> String
translateQualifiedName name =
  intercalate "." (translateNamespace name) ++ "." ++ translateName name

translateConstant :: Const -> String
translateConstant (I i)   = show i
translateConstant (BI i)  = show i
translateConstant (Fl f)  = show f
translateConstant (Ch c)  = show c
translateConstant (Str s) = show s
translateConstant IType   = "__IDR__.IntType"
translateConstant c       =
  "(function(){throw 'Unimplemented Const: " ++ show c ++ "';})()"

translateParameterlist =
  map translateParameter
  where translateParameter (MN i name) = name ++ show i
        translateParameter (UN name) = name

translateDeclaration :: NamespaceName -> SDecl -> String
translateDeclaration modname (SFun name params stackSize body) =
     modname
  ++ "."
  ++ translateName name
  ++ " = function("
  ++ intercalate "," p
  ++ "){\n"
  ++ concatMap assignVar (zip [0..] p)
  ++ concatMap allocVar [numP..(numP+stackSize-1)]
  ++ "return "
  ++ translateExpression modname body
  ++ ";\n};\n"
  where 
    numP :: Int
    numP = length params

    allocVar :: Int -> String
    allocVar n = "var __var_" ++ show n ++ ";\n"

    assignVar :: (Int, String) -> String
    assignVar (n, s) = "var __var_" ++ show n ++ " = " ++ s ++ ";\n"

    p :: [String]
    p = translateParameterlist params

translateVariableName :: LVar -> String
translateVariableName (Loc i) =
  "__var_" ++ show i

translateExpression :: NamespaceName -> SExp -> String
translateExpression modname (SLet name value body) =
     "(function("
  ++ translateVariableName name
  ++ "){\nreturn "
  ++ translateExpression modname body
  ++ ";\n})("
  ++ translateExpression modname value
  ++ ")"

translateExpression _ (SConst cst) =
  translateConstant cst

translateExpression _ (SV var) =
  translateVariableName var

translateExpression modname (SApp False name vars) =
  createTailcall $ translateFunctionCall name vars

translateExpression modname (SApp True name vars) =
     "(function(){\n"
  ++ "return new __IDR__.Tailcall("
  ++ "function(){\n"
  ++ "return " ++ translateFunctionCall name vars
  ++ ";\n});"
  ++ "\n})()"

translateExpression _ (SOp op vars)
  | LPlus       <- op
  , (lhs:rhs:_) <- vars = translateBinaryOp "+" lhs rhs
  | LMinus      <- op
  , (lhs:rhs:_) <- vars = translateBinaryOp "-" lhs rhs
  | LTimes      <- op
  , (lhs:rhs:_) <- vars = translateBinaryOp "*" lhs rhs
  | LDiv        <- op
  , (lhs:rhs:_) <- vars = translateBinaryOp "/" lhs rhs
  | LMod        <- op
  , (lhs:rhs:_) <- vars = translateBinaryOp "%" lhs rhs
  | LEq         <- op
  , (lhs:rhs:_) <- vars = translateBinaryOp "==" lhs rhs
  | LLt         <- op
  , (lhs:rhs:_) <- vars = translateBinaryOp "<" lhs rhs
  | LLe         <- op
  , (lhs:rhs:_) <- vars = translateBinaryOp "<=" lhs rhs
  | LGt         <- op
  , (lhs:rhs:_) <- vars = translateBinaryOp ">" lhs rhs
  | LGe         <- op
  , (lhs:rhs:_) <- vars = translateBinaryOp ">=" lhs rhs

  | LFPlus      <- op
  , (lhs:rhs:_) <- vars = translateBinaryOp "+" lhs rhs
  | LFMinus     <- op
  , (lhs:rhs:_) <- vars = translateBinaryOp "-" lhs rhs
  | LFTimes     <- op
  , (lhs:rhs:_) <- vars = translateBinaryOp "*" lhs rhs
  | LFDiv       <- op
  , (lhs:rhs:_) <- vars = translateBinaryOp "/" lhs rhs
  | LFEq        <- op
  , (lhs:rhs:_) <- vars = translateBinaryOp "==" lhs rhs
  | LFLt        <- op
  , (lhs:rhs:_) <- vars = translateBinaryOp "<" lhs rhs
  | LFLe        <- op
  , (lhs:rhs:_) <- vars = translateBinaryOp "<=" lhs rhs
  | LFGt        <- op
  , (lhs:rhs:_) <- vars = translateBinaryOp ">" lhs rhs
  | LFGe        <- op
  , (lhs:rhs:_) <- vars = translateBinaryOp ">=" lhs rhs

  | LBPlus      <- op
  , (lhs:rhs:_) <- vars = translateBinaryOp "+" lhs rhs
  | LBMinus     <- op
  , (lhs:rhs:_) <- vars = translateBinaryOp "-" lhs rhs
  | LBTimes     <- op
  , (lhs:rhs:_) <- vars = translateBinaryOp "*" lhs rhs
  | LBDiv       <- op
  , (lhs:rhs:_) <- vars = translateBinaryOp "/" lhs rhs
  | LBMod       <- op
  , (lhs:rhs:_) <- vars = translateBinaryOp "%" lhs rhs
  | LBEq        <- op
  , (lhs:rhs:_) <- vars = translateBinaryOp "==" lhs rhs
  | LBLt        <- op
  , (lhs:rhs:_) <- vars = translateBinaryOp "<" lhs rhs
  | LBLe        <- op
  , (lhs:rhs:_) <- vars = translateBinaryOp "<=" lhs rhs
  | LBGt        <- op
  , (lhs:rhs:_) <- vars = translateBinaryOp ">" lhs rhs
  | LBGe        <- op
  , (lhs:rhs:_) <- vars = translateBinaryOp ">=" lhs rhs

  | LStrConcat  <- op
  , (lhs:rhs:_) <- vars = translateBinaryOp "+" lhs rhs
  | LStrEq      <- op
  , (lhs:rhs:_) <- vars = translateBinaryOp "=" lhs rhs

  | LIntStr     <- op
  , (arg:_)     <- vars = "String(" ++ translateVariableName arg ++ ");"
  
  where
    translateBinaryOp :: String -> LVar -> LVar -> String
    translateBinaryOp f lhs rhs =
         translateVariableName lhs
      ++ f
      ++ translateVariableName rhs

translateExpression _ (SError msg) =
  "(function(){throw \'" ++ msg ++ "\';})();"

translateExpression _ (SForeign _ _ "putStr" [(FString, var)]) =
  "__IDR__.print(" ++ translateVariableName var ++ ");"

translateExpression _ (SForeign _ _ fun args) =
     fun
  ++ "("
  ++ intercalate "," (map (translateVariableName . snd) args)
  ++ ");"

translateExpression modname (SChkCase var cases) =
     "(function(e){\n"
  ++ intercalate " else " (map (translateCase modname "e") cases)
  ++ "\n})("
  ++ translateVariableName var
  ++ ")"

translateExpression modname (SCase var cases) = 
     "(function(e){\n"
  ++ intercalate " else " (map (translateCase modname "e") cases)
  ++ "\n})("
  ++ translateVariableName var
  ++ ")"

translateExpression _ (SCon i name vars) =
  concat [ "new __IDR__.Con("
         , show i
         , ","
         , '\'' : translateQualifiedName name ++ "\',["
         , intercalate "," $ map translateVariableName vars
         , "])"
         ]

translateExpression modname (SUpdate var e) =
  translateVariableName var ++ " = " ++ translateExpression modname e

translateExpression modname (SProj var i) =
  translateVariableName var ++ ".vars[" ++ show i ++"]"

translateExpression _ SNothing = "null"

translateExpression _ e =
     "(function(){throw 'Not yet implemented: "
  ++ filter (/= '\'') (show e)
  ++ "';})()"

translateCase :: String -> String -> SAlt -> String
translateCase modname _ (SDefaultCase e) =
  createIfBlock "true" (translateExpression modname e)

translateCase modname var (SConstCase cst e) =
  let cond = var ++ " == " ++ translateConstant cst in
      createIfBlock cond (translateExpression modname e)

translateCase modname var (SConCase a i name vars e) =
  let isCon = var ++ " instanceof __IDR__.Con"
      isI = show i ++ " == " ++ var ++ ".i"
      params = intercalate "," $ map (("__var_" ++) . show) [a..(a+length vars)]
      args = ".apply(this," ++ var ++ ".vars)"
      f b =
           "(function("
        ++ params 
        ++ "){\nreturn " ++ b ++ "\n})" ++ args
      cond = intercalate " && " [isCon, isI] in
      createIfBlock cond $ f (translateExpression modname e)

createIfBlock cond e =
     "if (" ++ cond ++") {\n"
  ++ "return " ++ e
  ++ ";\n}"

createTailcall call =
  "__IDR__.tailcall(function(){return " ++ call ++ "})"

translateFunctionCall name vars =
     concat (intersperse "." $ translateNamespace name)
  ++ "."
  ++ translateName name
  ++ "("
  ++ intercalate "," (map translateVariableName vars)
  ++ ")"
