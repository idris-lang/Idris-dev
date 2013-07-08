{-# LANGUAGE PatternGuards #-}

module IRTS.CodegenJavaScript (codegenJavaScript, JSTarget(..)) where

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
import System.Directory

idrNamespace :: String
idrNamespace = "__IDR__"

data JSTarget = Node | JavaScript deriving Eq

codegenJavaScript
  :: JSTarget
  -> [(Name, SDecl)]
  -> FilePath
  -> OutputType
  -> IO ()
codegenJavaScript target definitions filename outputType = do
  let (header, runtime) = case target of
                               Node ->
                                 ("#!/usr/bin/env node\n", "-node")
                               JavaScript ->
                                 ("", "-browser")
  path <- getDataDir
  idrRuntime <- readFile $ path ++ "/js/Runtime-common.js"
  tgtRuntime <- readFile $ concat [path, "/js/Runtime", runtime, ".js"]
  writeFile filename ( header
                   ++ idrRuntime
                   ++ tgtRuntime
                   ++ functions
                   ++ mainLoop)

  setPermissions filename (emptyPermissions { readable   = True
                                            , executable = target == Node
                                            , writable   = True
                                            })
  where
    def = map (first translateNamespace) definitions
 
    functions = concatMap translateDeclaration def

    mainLoop :: String
    mainLoop = intercalate "\n" [ "\nfunction main() {"
                                , createTailcall "__IDR__runMain0()"
                                , "}\n\nmain();\n"
                                ]

translateIdentifier :: String -> String
translateIdentifier =
  replaceReserved . concatMap replaceBadChars
  where replaceBadChars :: Char -> String
        replaceBadChars c
          | ' ' <- c = "_"
          | '_' <- c = "__"
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
translateConstant (BI i)  = "__IDRRT__bigInt('" ++ show i ++ "')"
translateConstant (Fl f)  = show f
translateConstant (Ch c)  = show c
translateConstant (Str s) = show s
translateConstant (AType (ATInt ITNative)) = "__IDRRT__Int"
translateConstant StrType = "__IDRRT__String"
translateConstant (AType (ATInt ITBig)) = "__IDRRT__Integer"
translateConstant (AType ATFloat)  = "__IDRRT__Float"
translateConstant PtrType = "__IDRRT__Ptr"
translateConstant Forgot  = "__IDRRT__Forgot"
translateConstant c       =
  "(function(){throw 'Unimplemented Const: " ++ show c ++ "';})()"

translateParameterlist =
  map translateParameter
  where translateParameter (MN i name) = translateIdentifier name ++ show i
        translateParameter (UN name) = translateIdentifier name

translateDeclaration :: ([String], SDecl) -> String
translateDeclaration (path, SFun name params stackSize body) =
     "var " ++ concat (path ++ [translateName name])
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
     "new __IDRRT__Tailcall("
  ++ "function(){\n"
  ++ "return " ++ translateFunctionCall name vars
  ++ ";\n})"

translateExpression (SOp op vars)
  | LNoOp       <- op = translateVariableName (last vars) ++ "/* NOOP */"

  | (LPlus (ATInt ITBig)) <- op
  , (lhs:rhs:_) <- vars = translateBinaryOp ".add(" lhs rhs  ++ ")"
  | (LMinus (ATInt ITBig)) <- op
  , (lhs:rhs:_) <- vars = translateBinaryOp ".minus(" lhs rhs ++ ")"
  | (LTimes (ATInt ITBig)) <- op
  , (lhs:rhs:_) <- vars = translateBinaryOp ".times(" lhs rhs ++ ")"
  | (LSDiv (ATInt ITBig)) <- op
  , (lhs:rhs:_) <- vars = translateBinaryOp ".divide(" lhs rhs ++ ")"
  | (LSRem (ATInt ITBig)) <- op
  , (lhs:rhs:_) <- vars = translateBinaryOp ".mod(" lhs rhs ++ ")"
  | (LEq (ATInt ITBig)) <- op
  , (lhs:rhs:_) <- vars = translateBinaryOp ".equals(" lhs rhs ++ ")"
  | (LLt (ATInt ITBig)) <- op
  , (lhs:rhs:_) <- vars = translateBinaryOp ".lesser(" lhs rhs ++ ")"
  | (LLe (ATInt ITBig)) <- op
  , (lhs:rhs:_) <- vars = translateBinaryOp ".lesserOrEquals(" lhs rhs ++ ")"
  | (LGt (ATInt ITBig)) <- op
  , (lhs:rhs:_) <- vars = translateBinaryOp ".greater(" lhs rhs ++ ")"
  | (LGe (ATInt ITBig)) <- op
  , (lhs:rhs:_) <- vars = translateBinaryOp ".greaterOrEquals(" lhs rhs ++ ")"

  | (LPlus ATFloat)  <- op
  , (lhs:rhs:_) <- vars = translateBinaryOp "+" lhs rhs
  | (LMinus ATFloat) <- op
  , (lhs:rhs:_) <- vars = translateBinaryOp "-" lhs rhs
  | (LTimes ATFloat) <- op
  , (lhs:rhs:_) <- vars = translateBinaryOp "*" lhs rhs
  | (LSDiv ATFloat)  <- op
  , (lhs:rhs:_) <- vars = translateBinaryOp "/" lhs rhs
  | (LEq ATFloat) <- op
  , (lhs:rhs:_) <- vars = translateBinaryOp "==" lhs rhs
  | (LLt ATFloat) <- op
  , (lhs:rhs:_) <- vars = translateBinaryOp "<" lhs rhs
  | (LLe ATFloat) <- op
  , (lhs:rhs:_) <- vars = translateBinaryOp "<=" lhs rhs
  | (LGt ATFloat) <- op
  , (lhs:rhs:_) <- vars = translateBinaryOp ">" lhs rhs
  | (LGe ATFloat) <- op
  , (lhs:rhs:_) <- vars = translateBinaryOp ">=" lhs rhs

  | (LPlus _)   <- op
  , (lhs:rhs:_) <- vars = translateBinaryOp "+" lhs rhs
  | (LMinus _)  <- op
  , (lhs:rhs:_) <- vars = translateBinaryOp "-" lhs rhs
  | (LTimes _)  <- op
  , (lhs:rhs:_) <- vars = translateBinaryOp "*" lhs rhs
  | (LSDiv _)   <- op
  , (lhs:rhs:_) <- vars = translateBinaryOp "/" lhs rhs
  | (LSRem _)   <- op
  , (lhs:rhs:_) <- vars = translateBinaryOp "%" lhs rhs
  | (LEq _)     <- op
  , (lhs:rhs:_) <- vars = translateBinaryOp "==" lhs rhs
  | (LLt _)     <- op
  , (lhs:rhs:_) <- vars = translateBinaryOp "<" lhs rhs
  | (LLe _)     <- op
  , (lhs:rhs:_) <- vars = translateBinaryOp "<=" lhs rhs
  | (LGt _)     <- op
  , (lhs:rhs:_) <- vars = translateBinaryOp ">" lhs rhs
  | (LGe _)     <- op
  , (lhs:rhs:_) <- vars = translateBinaryOp ">=" lhs rhs
  | (LAnd _)    <- op
  , (lhs:rhs:_) <- vars = translateBinaryOp "&" lhs rhs
  | (LOr _)     <- op
  , (lhs:rhs:_) <- vars = translateBinaryOp "|" lhs rhs
  | (LXOr _)    <- op
  , (lhs:rhs:_) <- vars = translateBinaryOp "^" lhs rhs
  | (LSHL _)    <- op
  , (lhs:rhs:_) <- vars = translateBinaryOp "<<" rhs lhs
  | (LASHR _)   <- op
  , (lhs:rhs:_) <- vars = translateBinaryOp ">>" rhs lhs
  | (LCompl _)  <- op
  , (arg:_)     <- vars = '~' : translateVariableName arg

  | LStrConcat  <- op
  , (lhs:rhs:_) <- vars = translateBinaryOp "+" lhs rhs
  | LStrEq      <- op
  , (lhs:rhs:_) <- vars = translateBinaryOp "==" lhs rhs
  | LStrLt      <- op
  , (lhs:rhs:_) <- vars = translateBinaryOp "<" lhs rhs
  | LStrLen     <- op
  , (arg:_)     <- vars = translateVariableName arg ++ ".length"

  | (LStrInt ITNative) <- op
  , (arg:_)     <- vars = "parseInt(" ++ translateVariableName arg ++ ")"
  | (LIntStr ITNative) <- op
  , (arg:_)     <- vars = "String(" ++ translateVariableName arg ++ ")"
  | (LSExt ITNative ITBig) <- op
  , (arg:_)     <- vars = "__IDRRT__bigInt(" ++ translateVariableName arg ++ ")"
  | (LTrunc ITBig ITNative) <- op
  , (arg:_)     <- vars = translateVariableName arg ++ ".valueOf()"
  | (LIntStr ITBig) <- op
  , (arg:_)     <- vars = translateVariableName arg ++ ".toString()"
  | (LStrInt ITBig) <- op
  , (arg:_)     <- vars = "__IDRRT__bigInt(" ++ translateVariableName arg ++ ")"
  | LFloatStr   <- op
  , (arg:_)     <- vars = "String(" ++ translateVariableName arg ++ ")"
  | LStrFloat   <- op
  , (arg:_)     <- vars = "parseFloat(" ++ translateVariableName arg ++ ")"
  | (LIntFloat ITNative) <- op
  , (arg:_)     <- vars = translateVariableName arg
  | (LFloatInt ITNative) <- op
  , (arg:_)     <- vars = translateVariableName arg
  | (LChInt ITNative) <- op
  , (arg:_)     <- vars = translateVariableName arg ++ ".charCodeAt(0)"
  | (LIntCh ITNative) <- op
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
                              v ++ ".split('').reverse().join('')"
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
  "(function(){throw \'" ++ msg ++ "\';})()"

translateExpression (SForeign _ _ "putStr" [(FString, var)]) =
  "__IDRRT__print(" ++ translateVariableName var ++ ")"

translateExpression (SForeign _ _ fun args)
  | "[]=" `isSuffixOf` fun
  , (obj:idx:val:[]) <- args =
    concat [object obj, index idx, assign val]

  | "[]" `isSuffixOf` fun
  , (obj:idx:[]) <- args =
    object obj ++ index idx

  | "[" `isPrefixOf` fun && "]=" `isSuffixOf` fun
  , (obj:val:[]) <- args =
    concat [object obj, '[' : name ++ "]", assign val]

  | "[" `isPrefixOf` fun && "]" `isSuffixOf` fun
  , (obj:[]) <- args =
    object obj ++ '[' : name ++ "]"

  | "." `isPrefixOf` fun, "=" `isSuffixOf` fun
  , (obj:val:[]) <- args =
    concat [object obj, field, assign val]

  | "." `isPrefixOf` fun
  , (obj:[]) <- args =
    object obj ++ field

  | "." `isPrefixOf` fun
  , (obj:[(FUnit, _)]) <- args =
    concat [object obj, method, "()"]
    
  | "." `isPrefixOf` fun
  , (obj:as) <- args =
    concat [object obj, method, arguments as]

  | "[]=" `isSuffixOf` fun
  , (idx:val:[]) <- args =
    concat [array, index idx, assign val]

  | "[]" `isSuffixOf` fun
  , (idx:[]) <- args =
    array ++ index idx

  | otherwise = fun ++ arguments args
  where
    name         = filter (`notElem` "[]=") fun
    method       = name
    field        = name
    array        = name
    object o     = translateVariableName (snd o)
    index  i     = "[" ++ translateVariableName (snd i) ++ "]"
    assign v     = '=' : generateWrapper v
    arguments as =
      '(' : intercalate "," (map generateWrapper as) ++ ")"

    generateWrapper (ffunc, name)
      | FFunction   <- ffunc = "__IDRRT__ffiWrap(" ++ translateVariableName name ++ ")"
      | FFunctionIO <- ffunc = "__IDRRT__ffiWrap(" ++ translateVariableName name ++ ")"

    generateWrapper (_, name) =
      translateVariableName name

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
  concat [ "new __IDRRT__Con("
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
  | StrType <- ty = matchHelper "String"
  | PtrType <- ty = matchHelper "Ptr"
  | Forgot  <- ty = matchHelper "Forgot"
  | (AType ATFloat) <- ty = matchHelper "Float"
  | (AType (ATInt ITBig)) <- ty = matchHelper "Integer"
  | (AType (ATInt ITNative)) <- ty = matchHelper "Int"
  | (AType (ATInt ITChar))  <- ty = matchHelper "Char"
  where
    matchHelper tyName = translateTypeMatch var tyName e

translateCase var (SConstCase cst@(BI _) e) =
  let cond = "__IDRRT__bigInt(" ++ var ++ ").equals(" ++ translateConstant cst ++ ")" in
      createIfBlock cond (translateExpression e)

translateCase var (SConstCase cst e) =
  let cond = var ++ " == " ++ translateConstant cst in
      createIfBlock cond (translateExpression e)

translateCase var (SConCase a i name vars e) =
  let isCon = var ++ " instanceof __IDRRT__Con"
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
                  ++ " instanceof __IDRRT__Type && "
                  ++ var ++ ".type == '"++ ty ++"'") e


createIfBlock cond e =
     "if (" ++ cond ++") {\n"
  ++ "return " ++ e
  ++ ";\n}"

createTailcall call =
  "__IDRRT__tailcall(function(){return " ++ call ++ "})"

translateFunctionCall name vars =
     concat (translateNamespace name)
  ++ translateName name
  ++ "("
  ++ intercalate "," (map translateVariableName vars)
  ++ ")"
