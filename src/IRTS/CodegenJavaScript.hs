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
import qualified Data.Map as Map
import System.IO

idrNamespace :: String
idrNamespace = "__IDR__"

codegenJavaScript
  :: [(Name, SDecl)]
  -> FilePath
  -> OutputType
  -> IO ()
codegenJavaScript definitions filename outputType = do
  path <- getDataDir
  idrRuntime <- readFile (path ++ "/js/Runtime.js")
  writeFile filename (idrRuntime ++ modules ++ functions ++ mainLoop)
  where
    def = map (first translateNamespace) definitions
 
    functions = concatMap translateDeclaration def

    mainLoop :: String
    mainLoop = intercalate "\n" [ "\nfunction main() {"
                                , createTailcall "__IDR__.runMain0()"
                                , "}\n\nmain();\n"
                                ]

    modules =
      concatMap allocMod mods
      where
        allocMod m = intercalate "." m ++ " = {};\n"
        sortMods a b = compare (length a) (length b)

        mods =
          drop 1 $ sortBy sortMods $ nub $ concatMap (inits . fst) def

translateIdentifier :: String -> String
translateIdentifier =
  replaceReserved . concatMap replaceBadChars
  where replaceBadChars :: Char -> String
        replaceBadChars c
          | isDigit c = "_" ++ [c] ++ "_"
          | not (isLetter c && isAscii c) = '_' : show (ord c)
          | otherwise = [c]
        replaceReserved s
          | s `elem` reserved = '_' : s
          | otherwise         = s
        reserved = [ "break"
                   , "case"
                   , "catch"
                   , "continue"
                   , "debugger"
                   , "default"
                   , "delete"
                   , "do"
                   , "else"
                   , "finally"
                   , "for"
                   , "function"
                   , "if"
                   , "in"
                   , "instanceof"
                   , "new"
                   , "return"
                   , "switch"
                   , "this"
                   , "throw"
                   , "try"
                   , "typeof"
                   , "var"
                   , "void"
                   , "while"
                   , "with"
                   
                   , "class"
                   , "enum"
                   , "export"
                   , "extends"
                   , "import"
                   , "super"
                   
                   , "implements"
                   , "interface"
                   , "let"
                   , "package"
                   , "private"
                   , "protected"
                   , "public"
                   , "static"
                   , "yield"
                   ]

translateNamespace :: Name -> [String]
translateNamespace (UN _)    = [idrNamespace]
translateNamespace (NS _ ns) = idrNamespace : map translateIdentifier ns
translateNamespace (MN _ _)  = [idrNamespace]

translateName :: Name -> String
translateName (UN name)   = translateIdentifier name
translateName (NS name _) = translateName name
translateName (MN i name) = translateIdentifier name ++ show i

translateConstant :: Const -> String
translateConstant (I i)   = show i
translateConstant (BI i)  = "__IDRRT__.bigInt('" ++ show i ++ "')"
translateConstant (Fl f)  = show f
translateConstant (Ch c)  = show c
translateConstant (Str s) = show s
translateConstant IType   = "__IDRRT__.Int"
translateConstant ChType  = "__IDRRT__.Char"
translateConstant StrType = "__IDRRT__.String"
translateConstant BIType  = "__IDRRT__.Integer"
translateConstant FlType  = "__IDRRT__.Float"
translateConstant Forgot  = "__IDRRT__.Forgot"
translateConstant c       =
  "(function(){throw 'Unimplemented Const: " ++ show c ++ "';})()"

translateParameterlist =
  map translateParameter
  where translateParameter (MN i name) = translateIdentifier name ++ show i
        translateParameter (UN name) = translateIdentifier name

translateDeclaration :: ([String], SDecl) -> String
translateDeclaration (path, SFun name params stackSize body) =
     intercalate "." (path ++ [translateName name])
  ++ " = function("
  ++ intercalate "," p
  ++ "){\n"
  ++ concatMap assignVar (zip [0..] p)
  ++ concatMap allocVar [numP..(numP+stackSize-1)]
  ++ "return "
  ++ translateExpression body
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

translateExpression :: SExp -> String
translateExpression (SLet name value body) =
     "(function("
  ++ translateVariableName name
  ++ "){\nreturn "
  ++ translateExpression body
  ++ ";\n})("
  ++ translateExpression value
  ++ ")"

translateExpression (SConst cst) =
  translateConstant cst

translateExpression (SV var) =
  translateVariableName var

translateExpression (SApp False name vars) =
  createTailcall $ translateFunctionCall name vars

translateExpression (SApp True name vars) =
     "new __IDRRT__.Tailcall("
  ++ "function(){\n"
  ++ "return " ++ translateFunctionCall name vars
  ++ ";\n});"

translateExpression (SOp op vars)
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
  | LAnd        <- op
  , (lhs:rhs:_) <- vars = translateBinaryOp "&" lhs rhs
  | LOr         <- op
  , (lhs:rhs:_) <- vars = translateBinaryOp "|" lhs rhs
  | LXOr        <- op
  , (lhs:rhs:_) <- vars = translateBinaryOp "^" lhs rhs
  | LSHL        <- op
  , (lhs:rhs:_) <- vars = translateBinaryOp "<<" rhs lhs
  | LSHR        <- op
  , (lhs:rhs:_) <- vars = translateBinaryOp ">>" rhs lhs
  | LCompl      <- op
  , (arg:_)     <- vars = '~' : translateVariableName arg

  | LBPlus      <- op
  , (lhs:rhs:_) <- vars = translateBinaryOp ".add(" lhs rhs  ++ ")"
  | LBMinus     <- op
  , (lhs:rhs:_) <- vars = translateBinaryOp ".minus(" lhs rhs ++ ")"
  | LBTimes     <- op
  , (lhs:rhs:_) <- vars = translateBinaryOp ".times(" lhs rhs ++ ")"
  | LBDiv       <- op
  , (lhs:rhs:_) <- vars = translateBinaryOp ".divide(" lhs rhs ++ ")"
  | LBMod       <- op
  , (lhs:rhs:_) <- vars = translateBinaryOp ".mod(" lhs rhs ++ ")"
  | LBEq        <- op
  , (lhs:rhs:_) <- vars = translateBinaryOp ".equals(" lhs rhs ++ ")"
  | LBLt        <- op
  , (lhs:rhs:_) <- vars = translateBinaryOp ".lesser(" lhs rhs ++ ")"
  | LBLe        <- op
  , (lhs:rhs:_) <- vars = translateBinaryOp ".lesserOrEquals(" lhs rhs ++ ")"
  | LBGt        <- op
  , (lhs:rhs:_) <- vars = translateBinaryOp ".greater(" lhs rhs ++ ")"
  | LBGe        <- op
  , (lhs:rhs:_) <- vars = translateBinaryOp ".greaterOrEquals(" lhs rhs ++ ")"

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

  | LStrConcat  <- op
  , (lhs:rhs:_) <- vars = translateBinaryOp "+" lhs rhs
  | LStrEq      <- op
  , (lhs:rhs:_) <- vars = translateBinaryOp "==" lhs rhs
  | LStrLt      <- op
  , (lhs:rhs:_) <- vars = translateBinaryOp "<" lhs rhs
  | LStrLen     <- op
  , (arg:_)     <- vars = translateVariableName arg ++ ".length"

  | LStrInt     <- op
  , (arg:_)     <- vars = "parseInt(" ++ translateVariableName arg ++ ")"
  | LIntStr     <- op
  , (arg:_)     <- vars = "String(" ++ translateVariableName arg ++ ")"
  | LIntBig     <- op
  , (arg:_)     <- vars = "__IDRRT__.bigInt(" ++ translateVariableName arg ++ ")"
  | LBigInt     <- op
  , (arg:_)     <- vars = translateVariableName arg ++ ".valueOf()"
  | LBigStr     <- op
  , (arg:_)     <- vars = translateVariableName arg ++ ".toString()"
  | LStrBig     <- op
  , (arg:_)     <- vars = "__IDRRT__.bigInt(" ++ translateVariableName arg ++ ")"
  | LFloatStr   <- op
  , (arg:_)     <- vars = "String(" ++ translateVariableName arg ++ ")"
  | LStrFloat   <- op
  , (arg:_)     <- vars = "parseFloat(" ++ translateVariableName arg ++ ")"
  | LIntFloat   <- op
  , (arg:_)     <- vars = translateVariableName arg
  | LFloatInt   <- op
  , (arg:_)     <- vars = translateVariableName arg
  | LChInt      <- op
  , (arg:_)     <- vars = translateVariableName arg ++ ".charCodeAt(0)"
  | LIntCh      <- op
  , (arg:_)     <- vars =
    "String.fromCharCode(" ++ translateVariableName arg ++ ")"

  | LFExp       <- op
  , (arg:_)     <- vars = "Math.exp(" ++ translateVariableName arg ++ ")"
  | LFLog       <- op
  , (arg:_)     <- vars = "Math.log(" ++ translateVariableName arg ++ ")"
  | LFSin       <- op
  , (arg:_)     <- vars = "Math.sin(" ++ translateVariableName arg ++ ")"
  | LFCos       <- op
  , (arg:_)     <- vars = "Math.cos(" ++ translateVariableName arg ++ ")"
  | LFTan       <- op
  , (arg:_)     <- vars = "Math.tan(" ++ translateVariableName arg ++ ")"
  | LFASin      <- op
  , (arg:_)     <- vars = "Math.asin(" ++ translateVariableName arg ++ ")"
  | LFACos      <- op
  , (arg:_)     <- vars = "Math.acos(" ++ translateVariableName arg ++ ")"
  | LFATan      <- op
  , (arg:_)     <- vars = "Math.atan(" ++ translateVariableName arg ++ ")"
  | LFSqrt      <- op
  , (arg:_)     <- vars = "Math.sqrt(" ++ translateVariableName arg ++ ")"
  | LFFloor     <- op
  , (arg:_)     <- vars = "Math.floor(" ++ translateVariableName arg ++ ")"
  | LFCeil      <- op
  , (arg:_)     <- vars = "Math.ceil(" ++ translateVariableName arg ++ ")"

  | LStrCons    <- op
  , (lhs:rhs:_) <- vars = translateBinaryOp "+" lhs rhs
  | LStrHead    <- op
  , (arg:_)     <- vars = translateVariableName arg ++ "[0]"
  | LStrRev     <- op
  , (arg:_)     <- vars = let v = translateVariableName arg in
                              v ++ "split('').reverse().join('')"
  | LStrIndex   <- op
  , (lhs:rhs:_) <- vars = let l = translateVariableName lhs
                              r = translateVariableName rhs in
                              l ++ "[" ++ r ++ "]"
  | LStrTail    <- op
  , (arg:_)     <- vars = let v = translateVariableName arg in
                              v ++ ".substr(1," ++ v ++ ".length-1)"
  where
    translateBinaryOp :: String -> LVar -> LVar -> String
    translateBinaryOp f lhs rhs =
         translateVariableName lhs
      ++ f
      ++ translateVariableName rhs

translateExpression (SError msg) =
  "(function(){throw \'" ++ msg ++ "\';})();"

translateExpression (SForeign _ _ "putStr" [(FString, var)]) =
  "__IDRRT__.print(" ++ translateVariableName var ++ ");"

translateExpression (SForeign _ _ fun args) =
     fun
  ++ "("
  ++ intercalate "," (map (translateVariableName . snd) args)
  ++ ");"

translateExpression (SChkCase var cases) =
     "(function(e){\n"
  ++ intercalate " else " (map (translateCase "e") cases)
  ++ "\n})("
  ++ translateVariableName var
  ++ ")"

translateExpression (SCase var cases) = 
     "(function(e){\n"
  ++ intercalate " else " (map (translateCase "e") cases)
  ++ "\n})("
  ++ translateVariableName var
  ++ ")"

translateExpression (SCon i name vars) =
  concat [ "new __IDRRT__.Con("
         , show i
         , ",["
         , intercalate "," $ map translateVariableName vars
         , "])"
         ]

translateExpression (SUpdate var e) =
  translateVariableName var ++ " = " ++ translateExpression e

translateExpression (SProj var i) =
  translateVariableName var ++ ".vars[" ++ show i ++"]"

translateExpression SNothing = "null"

translateExpression e =
     "(function(){throw 'Not yet implemented: "
  ++ filter (/= '\'') (show e)
  ++ "';})()"

translateCase :: String -> SAlt -> String
translateCase _ (SDefaultCase e) =
  createIfBlock "true" (translateExpression e)

translateCase var (SConstCase ty e)
  | ChType   <- ty = matchHelper "Char"
  | StrType  <- ty = matchHelper "String"
  | IType    <- ty = matchHelper "Int"
  | BIType   <- ty = matchHelper "Integer"
  | FlType   <- ty = matchHelper "Float"
  | PtrType  <- ty = matchHelper "Pointer"
  | Forgot   <- ty = matchHelper "Forgot"
  where
    matchHelper tyName = translateTypeMatch var tyName e

translateCase var (SConstCase cst@(BI _) e) =
  let cond = var ++ ".equals(" ++ translateConstant cst ++ ")" in
      createIfBlock cond (translateExpression e)

translateCase var (SConstCase cst e) =
  let cond = var ++ " == " ++ translateConstant cst in
      createIfBlock cond (translateExpression e)

translateCase var (SConCase a i name vars e) =
  let isCon = var ++ " instanceof __IDRRT__.Con"
      isI = show i ++ " == " ++ var ++ ".i"
      params = intercalate "," $ map (("__var_" ++) . show) [a..(a+length vars)]
      args = ".apply(this," ++ var ++ ".vars)"
      f b =
           "(function("
        ++ params 
        ++ "){\nreturn " ++ b ++ "\n})" ++ args
      cond = intercalate " && " [isCon, isI] in
      createIfBlock cond $ f (translateExpression e)

translateTypeMatch :: String -> String -> SExp -> String
translateTypeMatch var ty exp =
  let e = translateExpression exp in
      createIfBlock (var
                  ++ " instanceof __IDRRT__.Type && "
                  ++ var ++ ".type == '"++ ty ++"'") e


createIfBlock cond e =
     "if (" ++ cond ++") {\n"
  ++ "return " ++ e
  ++ ";\n}"

createTailcall call =
  "__IDRRT__.tailcall(function(){return " ++ call ++ "})"

translateFunctionCall name vars =
     concat (intersperse "." $ translateNamespace name)
  ++ "."
  ++ translateName name
  ++ "("
  ++ intercalate "," (map translateVariableName vars)
  ++ ")"
