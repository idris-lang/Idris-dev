{-|
Module      : IRTS.JavaScript.AST
Description : Data structures and functions used with the JavaScript codegen.
Copyright   :
License     : BSD3
Maintainer  : The Idris Community.
-}
{-# LANGUAGE OverloadedStrings, PatternGuards #-}
module IRTS.JavaScript.AST where

import Data.Char (isDigit)
import qualified Data.Text as T
import Data.Word

data JSType = JSIntTy
            | JSStringTy
            | JSIntegerTy
            | JSFloatTy
            | JSCharTy
            | JSPtrTy
            | JSForgotTy
            deriving Eq


data JSInteger = JSBigZero
               | JSBigOne
               | JSBigInt Integer
               | JSBigIntExpr JS
               deriving Eq


data JSNum = JSInt Int
           | JSFloat Double
           | JSInteger JSInteger
           deriving Eq


data JSWord = JSWord8 Word8
            | JSWord16 Word16
            | JSWord32 Word32
            | JSWord64 Word64
            deriving Eq


data JSAnnotation = JSConstructor deriving Eq


instance Show JSAnnotation where
  show JSConstructor = "constructor"


data JS = JSRaw String
        | JSIdent String
        | JSFunction [String] JS
        | JSType JSType
        | JSSeq [JS]
        | JSReturn JS
        | JSApp JS [JS]
        | JSNew String [JS]
        | JSError String
        | JSBinOp String JS JS
        | JSPreOp String JS
        | JSPostOp String JS
        | JSProj JS String
        | JSNull
        | JSUndefined
        | JSThis
        | JSTrue
        | JSFalse
        | JSArray [JS]
        | JSString String
        | JSNum JSNum
        | JSWord JSWord
        | JSAssign JS JS
        | JSAlloc String (Maybe JS)
        | JSIndex JS JS
        | JSSwitch JS [(JS, JS)] (Maybe JS)
        | JSCond [(JS, JS)]
        | JSTernary JS JS JS
        | JSParens JS
        | JSWhile JS JS
        | JSFFI String [JS]
        | JSAnnotation JSAnnotation JS
        | JSDelete JS
        | JSClear JS
        | JSNoop
        deriving Eq


data FFI = FFICode Char | FFIArg Int | FFIError String

ffi :: String -> [String] -> T.Text
ffi code args = let parsed = ffiParse code in
                    case ffiError parsed of
                         Just err -> error err
                         Nothing  -> renderFFI parsed args
  where
    ffiParse :: String -> [FFI]
    ffiParse ""           = []
    ffiParse ['%']        = [FFIError "FFI - Invalid positional argument"]
    ffiParse ('%':'%':ss) = FFICode '%' : ffiParse ss
    ffiParse ('%':s:ss)
      | isDigit s =
         FFIArg (
           read $ s : takeWhile isDigit ss
          ) : ffiParse (dropWhile isDigit ss)
      | otherwise =
          [FFIError "FFI - Invalid positional argument"]
    ffiParse (s:ss) = FFICode s : ffiParse ss


    ffiError :: [FFI] -> Maybe String
    ffiError []                 = Nothing
    ffiError ((FFIError s):xs)  = Just s
    ffiError (x:xs)             = ffiError xs


    renderFFI :: [FFI] -> [String] -> T.Text
    renderFFI [] _ = ""
    renderFFI (FFICode c : fs) args = c `T.cons` renderFFI fs args
    renderFFI (FFIArg i : fs) args
      | i < length args && i >= 0 =
            T.pack (args !! i)
          `T.append` renderFFI fs args
      | otherwise = error "FFI - Argument index out of bounds"

compileJS :: JS -> T.Text
compileJS = compileJS' 0

compileJS' :: Int -> JS -> T.Text
compileJS' indent JSNoop = ""

compileJS' indent (JSAnnotation annotation js) =
    "/** @"
  `T.append` T.pack (show annotation)
  `T.append` " */\n"
  `T.append` compileJS' indent js

compileJS' indent (JSDelete js) =
  "delete " `T.append` compileJS' 0 js

compileJS' indent (JSClear js) =
   compileJS' 0 js `T.append` " = undefined"

compileJS' indent (JSFFI raw args) =
  ffi raw (map (T.unpack . compileJS' indent) args)

compileJS' indent (JSRaw code) =
  T.pack code

compileJS' indent (JSIdent ident) =
  T.pack ident

compileJS' indent (JSFunction args body) =
      T.replicate indent " " `T.append` "function("
   `T.append` T.intercalate "," (map T.pack args)
   `T.append` "){\n"
   `T.append` compileJS' (indent + 2) body
   `T.append` "\n}\n"

compileJS' indent (JSType ty)
  | JSIntTy     <- ty = "i$Int"
  | JSStringTy  <- ty = "i$String"
  | JSIntegerTy <- ty = "i$Integer"
  | JSFloatTy   <- ty = "i$Float"
  | JSCharTy    <- ty = "i$Char"
  | JSPtrTy     <- ty = "i$Ptr"
  | JSForgotTy  <- ty = "i$Forgot"

compileJS' indent (JSSeq seq) =
  T.intercalate ";\n" (
    map (
      (T.replicate indent " " `T.append`) . (compileJS' indent)
    ) $ filter (/= JSNoop) seq
  ) `T.append` ";"

compileJS' indent (JSReturn val) =
  "return " `T.append` compileJS' indent val

compileJS' indent (JSApp lhs rhs)
  | JSFunction {} <- lhs =
    T.concat ["(", compileJS' indent lhs, ")(", args, ")"]
  | otherwise =
    T.concat [compileJS' indent lhs, "(", args, ")"]
  where args :: T.Text
        args = T.intercalate "," $ map (compileJS' 0) rhs

compileJS' indent (JSNew name args) =
    "new "
  `T.append` T.pack name
  `T.append` "("
  `T.append` T.intercalate "," (map (compileJS' 0) args)
  `T.append` ")"

compileJS' indent (JSError exc) =
  "(function(){throw new Error(\"" `T.append` T.pack exc `T.append` "\")})()"

compileJS' indent (JSBinOp op lhs rhs) =
    compileJS' indent lhs
  `T.append` " "
  `T.append` T.pack op
  `T.append` " "
  `T.append` compileJS' indent rhs

compileJS' indent (JSPreOp op val) =
  T.pack op `T.append` "(" `T.append` compileJS' indent val `T.append` ")"

compileJS' indent (JSProj obj field)
  | JSFunction {} <- obj =
    T.concat ["(", compileJS' indent obj, ").", T.pack field]
  | JSAssign {} <- obj =
    T.concat ["(", compileJS' indent obj, ").", T.pack field]
  | otherwise =
    compileJS' indent obj `T.append` ('.' `T.cons` T.pack field)

compileJS' indent JSNull =
  "null"

compileJS' indent JSUndefined =
  "undefined"

compileJS' indent JSThis =
  "this"

compileJS' indent JSTrue =
  "true"

compileJS' indent JSFalse =
  "false"

compileJS' indent (JSArray elems) =
  "[" `T.append` T.intercalate "," (map (compileJS' 0) elems) `T.append` "]"

compileJS' indent (JSString str) =
  "\"" `T.append` T.pack str `T.append` "\""

compileJS' indent (JSNum num)
  | JSInt i                    <- num = T.pack (show i)
  | JSFloat f                  <- num = T.pack (show f)
  | JSInteger JSBigZero        <- num = T.pack "i$ZERO"
  | JSInteger JSBigOne         <- num = T.pack "i$ONE"
  | JSInteger (JSBigInt i)     <- num = T.pack (show i)
  | JSInteger (JSBigIntExpr e) <- num =
      "i$bigInt(" `T.append` compileJS' indent e `T.append` ")"

compileJS' indent (JSAssign lhs rhs) =
  compileJS' indent lhs `T.append` " = " `T.append` compileJS' indent rhs

compileJS' 0 (JSAlloc name (Just val@(JSNew _ _))) =
    "var "
  `T.append` T.pack name
  `T.append` " = "
  `T.append` compileJS' 0 val
  `T.append` ";\n"

compileJS' indent (JSAlloc name val) =
    "var "
  `T.append` T.pack name
  `T.append` maybe "" ((" = " `T.append`) . compileJS' indent) val

compileJS' indent (JSIndex lhs rhs) =
    compileJS' indent lhs
  `T.append` "["
  `T.append` compileJS' indent rhs
  `T.append` "]"

compileJS' indent (JSCond branches) =
  T.intercalate " else " $ map createIfBlock branches
  where
    createIfBlock (JSNoop, e@(JSSeq _)) =
         "{\n"
      `T.append` compileJS' (indent + 2) e
      `T.append` "\n" `T.append` T.replicate indent " " `T.append` "}"
    createIfBlock (JSNoop, e) =
         "{\n"
      `T.append` compileJS' (indent + 2) e
      `T.append` ";\n" `T.append` T.replicate indent " " `T.append` "}"
    createIfBlock (cond, e@(JSSeq _)) =
         "if (" `T.append` compileJS' indent cond `T.append`") {\n"
      `T.append` compileJS' (indent + 2) e
      `T.append` "\n" `T.append` T.replicate indent " " `T.append` "}"
    createIfBlock (cond, e) =
         "if (" `T.append` compileJS' indent cond `T.append`") {\n"
      `T.append` T.replicate (indent + 2) " "
      `T.append` compileJS' (indent + 2) e
      `T.append` ";\n"
      `T.append` T.replicate indent " "
      `T.append` "}"

compileJS' indent (JSSwitch val [(_,JSSeq seq)] Nothing) =
  let (h,t) = splitAt 1 seq in
         (T.concat (map (compileJS' indent) h) `T.append` ";\n")
      `T.append` (
        T.intercalate ";\n" $ map (
          (T.replicate indent " " `T.append`) . compileJS' indent
        ) t
      )

compileJS' indent (JSSwitch val branches def) =
     "switch(" `T.append` compileJS' indent val `T.append` "){\n"
  `T.append` T.concat (map mkBranch branches)
  `T.append` mkDefault def
  `T.append` T.replicate indent " " `T.append` "}"
  where
    mkBranch :: (JS, JS) -> T.Text
    mkBranch (tag, code) =
         T.replicate (indent + 2) " "
      `T.append` "case "
      `T.append` compileJS' indent tag
      `T.append` ":\n"
      `T.append` compileJS' (indent + 4) code
      `T.append` "\n"
      `T.append` (T.replicate (indent + 4) " " `T.append` "break;\n")

    mkDefault :: Maybe JS -> T.Text
    mkDefault Nothing = ""
    mkDefault (Just def) =
         T.replicate (indent + 2) " " `T.append` "default:\n"
      `T.append` compileJS' (indent + 4)def
      `T.append` "\n"


compileJS' indent (JSTernary cond true false) =
  let c = compileJS' indent cond
      t = compileJS' indent true
      f = compileJS' indent false in
        "("
      `T.append` c
      `T.append` ")?("
      `T.append` t
      `T.append` "):("
      `T.append` f
      `T.append` ")"

compileJS' indent (JSParens js) =
  "(" `T.append` compileJS' indent js `T.append` ")"

compileJS' indent (JSWhile cond body) =
     "while (" `T.append` compileJS' indent cond `T.append` ") {\n"
  `T.append` compileJS' (indent + 2) body
  `T.append` "\n" `T.append` T.replicate indent " " `T.append` "}"

compileJS' indent (JSWord word)
  | JSWord8  b <- word =
      "new Uint8Array([" `T.append` T.pack (show b) `T.append` "])"
  | JSWord16 b <- word =
      "new Uint16Array([" `T.append` T.pack (show b) `T.append` "])"
  | JSWord32 b <- word =
      "new Uint32Array([" `T.append` T.pack (show b) `T.append` "])"
  | JSWord64 b <- word =
      "i$bigInt(\"" `T.append` T.pack (show b) `T.append` "\")"

jsInstanceOf :: JS -> String -> JS
jsInstanceOf obj cls = JSBinOp "instanceof" obj (JSIdent cls)

jsOr :: JS -> JS -> JS
jsOr lhs rhs = JSBinOp "||" lhs rhs

jsAnd :: JS -> JS -> JS
jsAnd lhs rhs = JSBinOp "&&" lhs rhs

jsMeth :: JS -> String -> [JS] -> JS
jsMeth obj meth args = JSApp (JSProj obj meth) args

jsCall :: String -> [JS] -> JS
jsCall fun args = JSApp (JSIdent fun) args

jsTypeOf :: JS -> JS
jsTypeOf js = JSPreOp "typeof " js

jsEq :: JS -> JS -> JS
jsEq lhs@(JSNum (JSInteger _)) rhs = JSApp (JSProj lhs "equals") [rhs]
jsEq lhs rhs@(JSNum (JSInteger _)) = JSApp (JSProj lhs "equals") [rhs]
jsEq lhs rhs = JSBinOp "==" lhs rhs

jsNotEq :: JS -> JS -> JS
jsNotEq lhs rhs = JSBinOp "!=" lhs rhs

jsIsNumber :: JS -> JS
jsIsNumber js = (jsTypeOf js) `jsEq` (JSString "number")

jsIsNull :: JS -> JS
jsIsNull js = JSBinOp "==" js JSNull

jsBigInt :: JS -> JS
jsBigInt (JSString "0") = JSNum (JSInteger JSBigZero)
jsBigInt (JSString "1") = JSNum (JSInteger JSBigOne)
jsBigInt js             = JSNum $ JSInteger $ JSBigIntExpr js

jsUnPackBits :: JS -> JS
jsUnPackBits js = JSIndex js $ JSNum (JSInt 0)

jsPackUBits8 :: JS -> JS
jsPackUBits8 js = JSNew "Uint8Array" [JSArray [js]]

jsPackUBits16 :: JS -> JS
jsPackUBits16 js = JSNew "Uint16Array" [JSArray [js]]

jsPackUBits32 :: JS -> JS
jsPackUBits32 js = JSNew "Uint32Array" [JSArray [js]]

jsPackSBits8 :: JS -> JS
jsPackSBits8 js = JSNew "Int8Array" [JSArray [js]]

jsPackSBits16 :: JS -> JS
jsPackSBits16 js = JSNew "Int16Array" [JSArray [js]]

jsPackSBits32 :: JS -> JS
jsPackSBits32 js = JSNew "Int32Array" [JSArray [js]]
