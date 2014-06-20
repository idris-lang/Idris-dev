{-# LANGUAGE PatternGuards #-}

module IRTS.CodegenJavaScript (codegenJavaScript, codegenNode, JSTarget(..)) where

import Idris.AbsSyntax hiding (TypeCase)
import IRTS.Bytecode
import IRTS.Lang
import IRTS.Simplified
import IRTS.CodegenCommon
import Idris.Core.TT
import Paths_idris
import Util.System

import Control.Arrow
import Control.Applicative ((<$>), (<*>), pure)
import Data.Char
import Numeric
import Data.List
import Data.Maybe
import Data.Word
import System.IO
import System.Directory


idrNamespace :: String
idrNamespace    = "__IDR__"
idrRTNamespace  = "__IDRRT__"
idrLTNamespace  = "__IDRLT__"
idrCTRNamespace = "__IDRCTR__"


data JSTarget = Node | JavaScript deriving Eq


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
        | JSVar LVar
        | JSNull
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
        | JSTernary JS JS JS
        | JSParens JS
        | JSWhile JS JS
        | JSFFI String [JS]
        | JSAnnotation JSAnnotation JS
        | JSNoop
        deriving Eq


data FFI = FFICode Char | FFIArg Int | FFIError String

compileJS :: JS -> String
compileJS JSNoop = ""

compileJS (JSAnnotation annotation js) =
  "/** @" ++ show annotation ++ " */\n" ++ compileJS js

{-compileJS (JSFFI raw args) =-}
  {-ffi raw (map compileJS args)-}

compileJS (JSRaw code) =
  code

compileJS (JSIdent ident) =
  ident

compileJS (JSFunction args body) =
     "function("
   ++ intercalate "," args
   ++ "){\n"
   ++ compileJS body
   ++ "\n}\n"

compileJS (JSType ty)
  | JSIntTy     <- ty = idrRTNamespace ++ "Int"
  | JSStringTy  <- ty = idrRTNamespace ++ "String"
  | JSIntegerTy <- ty = idrRTNamespace ++ "Integer"
  | JSFloatTy   <- ty = idrRTNamespace ++ "Float"
  | JSCharTy    <- ty = idrRTNamespace ++ "Char"
  | JSPtrTy     <- ty = idrRTNamespace ++ "Ptr"
  | JSForgotTy  <- ty = idrRTNamespace ++ "Forgot"

compileJS (JSSeq seq) =
  intercalate ";\n" (map compileJS $ filter (/= JSNoop) seq)

compileJS (JSReturn val) =
  "return " ++ compileJS val

compileJS (JSApp lhs rhs)
  | JSFunction {} <- lhs =
    concat ["(", compileJS lhs, ")(", args, ")"]
  | otherwise =
    concat [compileJS lhs, "(", args, ")"]
  where args :: String
        args = intercalate "," $ map compileJS rhs

compileJS (JSNew name args) =
  "new " ++ name ++ "(" ++ intercalate "," (map compileJS args) ++ ")"

compileJS (JSError exc) =
  "throw new Error(\"" ++ exc ++ "\")"

compileJS (JSBinOp op lhs rhs) =
  compileJS lhs ++ " " ++ op ++ " " ++ compileJS rhs

compileJS (JSPreOp op val) =
  op ++ compileJS val

compileJS (JSProj obj field)
  | JSFunction {} <- obj =
    concat ["(", compileJS obj, ").", field]
  | JSAssign {} <- obj =
    concat ["(", compileJS obj, ").", field]
  | otherwise =
    compileJS obj ++ '.' : field

{-compileJS (JSVar var) =-}
  {-translateVariableName var-}

compileJS JSNull =
  "null"

compileJS JSThis =
  "this"

compileJS JSTrue =
  "true"

compileJS JSFalse =
  "false"

compileJS (JSArray elems) =
  "[" ++ intercalate "," (map compileJS elems) ++ "]"

compileJS (JSString str) =
  "\"" ++ str ++ "\""

compileJS (JSNum num)
  | JSInt i                <- num = show i
  | JSFloat f              <- num = show f
  | JSInteger JSBigZero    <- num = "__IDRRT__ZERO"
  | JSInteger JSBigOne     <- num = "__IDRRT__ONE"
  | JSInteger (JSBigInt i) <- num = show i

compileJS (JSAssign lhs rhs) =
  compileJS lhs ++ " = " ++ compileJS rhs

compileJS (JSAlloc name val) =
  "var " ++ name ++ maybe "" ((" = " ++) . compileJS) val

compileJS (JSIndex lhs rhs) =
  compileJS lhs ++ "[" ++ compileJS rhs ++ "]"

compileJS (JSSwitch cond branches def) =
     "switch(" ++ compileJS cond ++ "){\n"
  ++ concatMap mkBranch branches
  ++ mkDefault def
  ++ "}"
  where
    mkBranch :: (JS, JS) -> String
    mkBranch (tag, code) =
         "case " ++ compileJS tag ++ ":\n"
      ++ compileJS code
      ++ "\nbreak;\n"

    mkDefault :: Maybe JS -> String
    mkDefault Nothing = ""
    mkDefault (Just def) =
         "default:\n"
      ++ compileJS def
      ++ "\n"


compileJS (JSTernary cond true false) =
  let c = compileJS cond
      t = compileJS true
      f = compileJS false in
      "(" ++ c ++ ")?(" ++ t ++ "):(" ++ f ++ ")"

compileJS (JSParens js) =
  "(" ++ compileJS js ++ ")"

compileJS (JSWhile cond body) =
     "while (" ++ compileJS cond ++ ") {\n"
  ++ compileJS body
  ++ "\n}"

compileJS (JSWord word)
  | JSWord8  b <- word = "new Uint8Array([" ++ show b ++ "])"
  | JSWord16 b <- word = "new Uint16Array([" ++ show b ++ "])"
  | JSWord32 b <- word = "new Uint32Array([" ++ show b ++ "])"
  | JSWord64 b <- word = idrRTNamespace ++ "bigInt(\"" ++ show b ++ "\")"

codegenJavaScript :: CodeGenerator
codegenJavaScript ci = codegenJS_all JavaScript (simpleDecls ci)
                              (includes ci) (outputFile ci) (outputType ci)

codegenNode :: CodeGenerator
codegenNode ci = codegenJS_all Node (simpleDecls ci)
                        (includes ci) (outputFile ci) (outputType ci)

codegenJS_all
  :: JSTarget
  -> [(Name, SDecl)]
  -> [FilePath]
  -> FilePath
  -> OutputType
  -> IO ()
codegenJS_all target definitions includes filename outputType = do
  let code = map (compileJS . translateDecl . toBC) definitions
  let (header, rt) = case target of
                               Node ->
                                 ("#!/usr/bin/env node\n", "-node")
                               JavaScript ->
                                 ("", "-browser")
  path       <- (++) <$> getDataDir <*> (pure "/jsrts/")
  idrRuntime <- readFile $ path ++ "Runtime-common.js"
  tgtRuntime <- readFile $ concat [path, "Runtime", rt, ".js"]
  let runtime = header ++ idrRuntime ++ tgtRuntime
  writeFile filename $ runtime ++ concat code ++ main ++ invokeMain
    where
      main :: String
      main = compileJS $
        JSAlloc "main" $ Just $ JSFunction [] (
          JSSeq [ JSAlloc "vm" (Just $ JSNew "i$VM" [])
                , JSApp (JSIdent "mrunMain0") [ JSIdent "vm"
                                              , JSNum (JSInt 0)
                                              ]
                ]
        )

      invokeMain :: String
      invokeMain = compileJS $ JSApp (JSIdent "main") []


translateDecl :: (Name, [BC]) -> JS
translateDecl (name, bc) =
  JSAlloc (
    translateName name
  ) (Just $ JSFunction ["vm", "oldbase"] (
      JSSeq $ JSAlloc "myoldbase" Nothing : map translateBC bc)
    )

translateReg :: Reg -> JS
translateReg reg
  | RVal <- reg = JSProj (JSIdent "vm") "ret"
  | Tmp  <- reg = JSProj (JSIdent "vm") "reg1"
  | L 0  <- reg =
      JSIndex (
        JSProj (JSIdent "vm") "valstack"
      ) (JSProj (JSIdent "vm") "valstack_base")
  | L n  <- reg =
      JSIndex (
        JSProj (JSIdent "vm") "valstack"
      ) (
        JSBinOp "+" (JSProj (JSIdent "vm") "valstack_base") (JSNum (JSInt n))
      )
  | T 0  <- reg =
      JSIndex (
        JSProj (JSIdent "vm") "valstack"
      ) (JSProj (JSIdent "vm") "valstack_top")
  | T n  <- reg =
      JSIndex (
        JSProj (JSIdent "vm") "valstack"
      ) (
        JSBinOp "+" (JSProj (JSIdent "vm") "valstack_top") (JSNum (JSInt n))
      )

translateConstant :: Const -> JS
translateConstant (I i)                    = JSNum (JSInt i)
translateConstant (Fl f)                   = JSNum (JSFloat f)
translateConstant (Ch c)                   = JSString $ translateChar c
translateConstant (Str s)                  = JSString $ concatMap translateChar s
translateConstant (AType (ATInt ITNative)) = JSType JSIntTy
translateConstant StrType                  = JSType JSStringTy
translateConstant (AType (ATInt ITBig))    = JSType JSIntegerTy
translateConstant (AType ATFloat)          = JSType JSFloatTy
translateConstant (AType (ATInt ITChar))   = JSType JSCharTy
translateConstant PtrType                  = JSType JSPtrTy
translateConstant Forgot                   = JSType JSForgotTy
{-translateConstant (BI i)                   = jsBigInt $ JSString (show i)-}
translateConstant (BI i)                   = JSRaw $ show i
translateConstant (B8 b)                   = JSWord (JSWord8 b)
translateConstant (B16 b)                  = JSWord (JSWord16 b)
translateConstant (B32 b)                  = JSWord (JSWord32 b)
translateConstant (B64 b)                  = JSWord (JSWord64 b)
translateConstant c =
  jsERROR $ "Unimplemented Constant: " ++ show c


translateChar :: Char -> String
translateChar ch
  | '\a'   <- ch       = "\\u0007"
  | '\b'   <- ch       = "\\b"
  | '\f'   <- ch       = "\\f"
  | '\n'   <- ch       = "\\n"
  | '\r'   <- ch       = "\\r"
  | '\t'   <- ch       = "\\t"
  | '\v'   <- ch       = "\\v"
  | '\SO'  <- ch       = "\\u000E"
  | '\DEL' <- ch       = "\\u007F"
  | '\\'   <- ch       = "\\\\"
  | '\"'   <- ch       = "\\\""
  | '\''   <- ch       = "\\\'"
  | ch `elem` asciiTab = "\\u00" ++ fill (showIntAtBase 16 intToDigit (ord ch) "")
  | otherwise          = [ch]
  where
    fill :: String -> String
    fill s = if length s == 1
                then '0' : s
                else s

    asciiTab =
      ['\NUL', '\SOH', '\STX', '\ETX', '\EOT', '\ENQ', '\ACK', '\BEL',
       '\BS',  '\HT',  '\LF',  '\VT',  '\FF',  '\CR',  '\SO',  '\SI',
       '\DLE', '\DC1', '\DC2', '\DC3', '\DC4', '\NAK', '\SYN', '\ETB',
       '\CAN', '\EM',  '\SUB', '\ESC', '\FS',  '\GS',  '\RS',  '\US']
translateIdentifier :: String -> String
translateIdentifier =
  replaceReserved . concatMap replaceBadChars
  where replaceBadChars :: Char -> String
        replaceBadChars c
          | ' ' <- c  = "_"
          | '_' <- c  = "__"
          | isDigit c = '_' : show (ord c)
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

translateNamespace :: Name -> String
translateNamespace (UN _)    = idrNamespace
translateNamespace (NS _ ns) = idrNamespace ++ concatMap (translateIdentifier . str) ns
translateNamespace (MN _ _)  = idrNamespace
translateNamespace (SN name) = idrNamespace ++ translateSpecialName name
translateNamespace NErased   = idrNamespace

translateName :: Name -> String
translateName (UN name)   = 'u' : translateIdentifier (str name)
translateName (NS name _) = 'n' : translateName name
translateName (MN i name) = 'm' : translateIdentifier (str name) ++ show i
translateName (SN name)   = 's' : translateSpecialName name
translateName NErased     = "e"

translateSpecialName :: SpecialName -> String
translateSpecialName name
  | WhereN i m n  <- name =
    'w' : translateName m ++ translateName n ++ show i
  | InstanceN n s <- name =
    'i' : translateName n ++ concatMap (translateIdentifier . str) s
  | ParentN n s   <- name =
    'p' : translateName n ++ translateIdentifier (str s)
  | MethodN n     <- name =
    'm' : translateName n
  | CaseN n       <- name =
    'c' : translateName n

jsASSIGN :: Reg -> Reg -> JS
jsASSIGN r1 r2 = JSAssign (translateReg r1) (translateReg r2)

jsASSIGNCONST :: Reg -> Const -> JS
jsASSIGNCONST r c = JSAssign (translateReg r) (translateConstant c)

jsCALL :: Name -> JS
jsCALL n = JSApp (JSIdent (translateName n)) [JSIdent "vm", JSIdent "myoldbase"]

jsTAILCALL :: Name -> JS
jsTAILCALL n = JSApp (JSIdent (translateName n)) [JSIdent "vm", JSIdent "oldbase"]

jsFOREIGN :: Reg -> String -> [(FType, Reg)] -> JS
jsFOREIGN reg n args =
  JSAssign (translateReg reg) (JSApp (JSIdent n) (map extract args))
    where
      extract :: (FType, Reg) -> JS
      extract (ty, reg) =
        JSIndex (JSProj (translateReg reg) "args") (JSNum (JSInt 0))

jsREBASE :: JS
jsREBASE =
  JSAssign (
    JSProj (JSIdent "vm") "valstack_base"
  ) (
    JSIdent "oldbase"
  )

jsSTOREOLD :: JS
jsSTOREOLD =
  JSAssign (
    JSIdent "myoldbase"
  ) (
    JSProj (JSIdent "vm") "valstack_base"
  )

jsADDTOP :: Int -> JS
jsADDTOP n
  | 0 <- n    = JSNoop
  | otherwise =
      JSBinOp "+=" (JSProj (JSIdent "vm") "valstack_top") (JSNum (JSInt n))

jsTOPBASE :: Int -> JS
jsTOPBASE n
  | 0 <- n =
      JSAssign (
        JSProj (JSIdent "vm") "valstack_top"
      ) (
        JSProj (JSIdent "vm") "valstack_base"
      )
  | otherwise =
      JSAssign (
        JSProj (JSIdent "vm") "valstack_top"
      ) (
        JSBinOp "+" (JSProj (JSIdent "vm") "valstack_base") (JSNum (JSInt n))
      )

jsBASETOP :: Int -> JS
jsBASETOP n
  | 0 <- n =
      JSAssign (
        JSProj (JSIdent "vm") "valstack_base"
      ) (
        JSProj (JSIdent "vm") "valstack_top"
      )
  | otherwise =
      JSAssign (
        JSProj (JSIdent "vm") "valstack_base"
      ) (
        JSBinOp "+" (JSProj (JSIdent "vm") "valstack_top") (JSNum (JSInt n))
      )

jsNULL :: Reg -> JS
jsNULL r = JSAssign (translateReg r) JSNull

jsERROR :: String -> JS
jsERROR = JSError

jsSLIDE :: Int -> JS
jsSLIDE n = JSApp (JSIdent "i$SLIDE") [JSIdent "vm", JSNum (JSInt n)]

jsMKCON :: Reg -> Int -> [Reg] -> JS
jsMKCON r t rs =
  JSAssign (translateReg r) (
    JSNew "i$CON" [JSNum (JSInt t), JSArray (map translateReg rs)]
  )

jsInstanceOf :: JS -> String -> JS
jsInstanceOf obj cls = JSBinOp "instanceof" obj (JSIdent cls)

jsOr :: JS -> JS -> JS
jsOr lhs rhs = JSBinOp "||" lhs rhs

jsTypeOf :: JS -> JS
jsTypeOf js = JSPreOp "typeof " js

jsEq :: JS -> JS -> JS
jsEq = JSBinOp "=="

jsIsNumber :: JS -> JS
jsIsNumber js = (jsTypeOf js) `jsEq` (JSString "number")

jsIsNull :: JS -> JS
jsIsNull js = JSBinOp "==" js JSNull

jsTAG :: JS -> JS
jsTAG js =
  JSTernary (jsIsNumber js `jsOr` jsIsNull js) (
    JSNum (JSInt $ negate 1)
  ) (JSTernary (js `jsInstanceOf` "i$CON") (
      JSProj js "tag"
    ) (JSNum (JSInt $ negate 1)))

jsCTAG :: JS -> JS
jsCTAG js = JSProj js "tag"

-- TODO unsafe
jsCASE :: Bool -> Reg -> [(Int, [BC])] -> Maybe [BC] -> JS
jsCASE safe reg cases def =
  {-JSSwitch (tag safe (translateReg reg)) (-}
  JSSwitch (JSTernary (translateReg reg `jsInstanceOf` "i$CON") (
  JSProj (translateReg reg) "tag") (JSNum (JSInt $ negate 1))) (
    map ((JSNum . JSInt) *** prepBranch) cases
  ) (fmap prepBranch def)
    where
      tag :: Bool -> JS -> JS
      tag True  = jsCTAG
      tag False = jsTAG
      prepBranch :: [BC] -> JS
      prepBranch bc = JSSeq $ map translateBC bc

jsCONSTCASE :: Reg -> [(Const, [BC])] -> Maybe [BC] -> JS
jsCONSTCASE reg cases def =
  JSSwitch (translateReg reg) (
    map (translateConstant *** prepBranch) cases
  ) (fmap prepBranch def)
    where
      prepBranch :: [BC] -> JS
      prepBranch bc = JSSeq $ map translateBC bc

jsPROJECT :: Reg -> Int -> Int -> JS
jsPROJECT reg loc ar =
  JSApp (JSIdent "i$PROJECT") [ JSIdent "vm"
                              , translateReg reg
                              , JSNum (JSInt loc)
                              , JSNum (JSInt ar)
                              ]

jsOP :: Reg -> PrimFn -> [Reg] -> JS
jsOP reg op args = JSAssign (translateReg reg) jsOP'
  where
    jsOP' :: JS
    jsOP'
      | LStrConcat  <- op
      , (lhs:rhs:_) <- args = JSBinOp "+" (translateReg lhs) (translateReg rhs)
      | LPlus _     <- op
      , (lhs:rhs:_) <- args = JSBinOp "+" (translateReg lhs) (translateReg rhs)
      | LMinus _    <- op
      , (lhs:rhs:_) <- args = JSBinOp "-" (translateReg lhs) (translateReg rhs)
      | LIntStr _   <- op
      , (arg:_)     <- args = JSApp (JSIdent "String") [translateReg arg]
      | LEq _       <- op
      , (lhs:rhs:_) <- args = JSBinOp "==" (translateReg lhs) (translateReg rhs)
      | LSLt _      <- op
      , (lhs:rhs:_) <- args = JSBinOp "<" (translateReg lhs) (translateReg rhs)
      | otherwise           = JSRaw $ show op

jsRESERVE :: Int -> JS
jsRESERVE n = JSNoop -- JSApp (JSIdent "i$RESERVE") [JSIdent "vm", JSNum $ JSInt n]

translateBC :: BC -> JS
translateBC bc
  | ASSIGN r1 r2          <- bc = jsASSIGN r1 r2
  | ASSIGNCONST r c       <- bc = jsASSIGNCONST r c
  | UPDATE r1 r2          <- bc = jsASSIGN r1 r2
  | ADDTOP n              <- bc = jsADDTOP n
  | NULL r                <- bc = jsNULL r
  | CALL n                <- bc = jsCALL n
  | TAILCALL n            <- bc = jsTAILCALL n
  | FOREIGNCALL r _ _ n a <- bc = jsFOREIGN r n a
  | TOPBASE n             <- bc = jsTOPBASE n
  | BASETOP n             <- bc = jsBASETOP n
  | STOREOLD              <- bc = jsSTOREOLD
  | SLIDE n               <- bc = jsSLIDE n
  | REBASE                <- bc = jsREBASE
  | RESERVE n             <- bc = jsRESERVE n
  | MKCON r t rs          <- bc = jsMKCON r t rs
  | CASE s r c d          <- bc = jsCASE s r c d
  | CONSTCASE r c d       <- bc = jsCONSTCASE r c d
  | PROJECT r l a         <- bc = jsPROJECT r l a
  | OP r o a              <- bc = jsOP r o a
  | otherwise                   = JSRaw $ show bc
  {-| PROJECTINTO _ _ _     <- bc = undefined-}
  {-| ERROR e               <- bc = jsERROR e-}

