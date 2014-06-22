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

data CompileInfo = CompileInfo { compileInfoApplyCases :: [Int]
                               , compileInfoEvalCases  :: [Int]
                               }


initCompileInfo :: [(Name, [BC])] -> CompileInfo
initCompileInfo bc = CompileInfo (collectApplyCases bc) []
  where
    collectApplyCases :: [(Name, [BC])] -> [Int]
    collectApplyCases bc = getCases $ findApply bc

    findApply :: [(Name, [BC])] -> [BC]
    findApply ((MN 0 fun, bc):_)
      | fun == txt "APPLY" = bc
    findApply (_:bc) = findApply bc

    getCases :: [BC] -> [Int]
    getCases = concatMap analyze
      where
        analyze :: BC -> [Int]
        analyze (CASE _ _ b _) = map fst b
        analyze _              = []


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
  intercalate ";\n" (map compileJS $ filter (/= JSNoop) seq) ++ ";"

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

compileJS JSNull =
  "null"

compileJS JSUndefined =
  "undefined"

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
  | JSInt i                    <- num = show i
  | JSFloat f                  <- num = show f
  | JSInteger JSBigZero        <- num = "__IDRRT__ZERO"
  | JSInteger JSBigOne         <- num = "__IDRRT__ONE"
  | JSInteger (JSBigInt i)     <- num = show i
  | JSInteger (JSBigIntExpr e) <- num = "__IDRRT__bigInt(" ++ compileJS e ++ ")"

compileJS (JSAssign lhs rhs) =
  compileJS lhs ++ " = " ++ compileJS rhs

compileJS (JSAlloc name val) =
  "var " ++ name ++ maybe "" ((" = " ++) . compileJS) val

compileJS (JSIndex lhs rhs) =
  compileJS lhs ++ "[" ++ compileJS rhs ++ "]"

compileJS (JSCond branches) =
  intercalate " else " $ map createIfBlock branches
  where
    createIfBlock (JSNoop, e) =
         "{\n"
      ++ compileJS e
      ++ ";\n}"
    createIfBlock (cond, e) =
         "if (" ++ compileJS cond ++") {\n"
      ++ compileJS e
      ++ ";\n}"

compileJS (JSSwitch val branches def) =
     "switch(" ++ compileJS val ++ "){\n"
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
  let bytecode = map toBC definitions
  let info = initCompileInfo bytecode
  let code = concat $ map ((concatMap compileJS) . (translateDecl info)) bytecode
  let (header, rt) = case target of
                               Node ->
                                 ("#!/usr/bin/env node\n", "-node")
                               JavaScript ->
                                 ("", "-browser")
  path       <- (++) <$> getDataDir <*> (pure "/jsrts/")
  idrRuntime <- readFile $ path ++ "Runtime-common.js"
  tgtRuntime <- readFile $ concat [path, "Runtime", rt, ".js"]
  jsbn       <- readFile $ path ++ "jsbn/jsbn.js"
  let runtime = header ++ jsbn ++ idrRuntime ++ tgtRuntime
  writeFile filename $ runtime ++ code ++ main ++ invokeMain
  setPermissions filename (emptyPermissions { readable   = True
                                             , executable = target == Node
                                             , writable   = True
                                             })
    where
      main :: String
      main = compileJS $
        JSAlloc "main" $ Just $ JSFunction [] (
          JSSeq [ JSAlloc "vm" (Just $ JSNew "i$VM" [])
                , JSApp (
                    JSIdent (translateName (sMN 0 "runMain"))
                   ) [ JSIdent "vm"
                     , JSNum (JSInt 0)
                     ]
                ]
        )

      invokeMain :: String
      invokeMain = compileJS $ JSApp (JSIdent "main") []


translateDecl :: CompileInfo -> (Name, [BC]) -> [JS]
translateDecl info (name@(MN 0 fun), bc)
  | txt "APPLY" == fun =
         allocCaseFunctions (snd body)
      ++ [ JSAlloc (
               translateName name
           ) (Just $ JSFunction ["vm", "oldbase"] (
               JSSeq $ JSAlloc "myoldbase" Nothing : map (translateBC info) (fst body) ++ [
                 JSCond [ ( (translateReg $ caseReg (snd body)) `jsInstanceOf` "i$CON"
                          , JSApp (JSProj (translateReg $ caseReg (snd body)) "app") [ JSIdent "vm"
                                                                                     , JSIdent "oldbase"
                                                                                     , JSIdent "myoldbase"
                                                                                     ]
                          )
                          , ( JSNoop
                            , JSSeq $ map (translateBC info) (defaultCase (snd body))
                            )
                        ]
               ]
             )
           )
         ]
  where
    body :: ([BC], [BC])
    body = break isCase bc

    isCase :: BC -> Bool
    isCase bc
      | CASE _ _ _ _ <- bc = True
      | otherwise          = False

    defaultCase :: [BC] -> [BC]
    defaultCase ((CASE _ _ _ (Just d)):_) = d

    caseReg :: [BC] -> Reg
    caseReg ((CASE _ r _ _):_) = r

    allocCaseFunctions :: [BC] -> [JS]
    allocCaseFunctions ((CASE _ _ c _):_) = splitBranches c
    allocCaseFunctions _                  = []

    splitBranches :: [(Int, [BC])] -> [JS]
    splitBranches = map prepBranch

    prepBranch :: (Int, [BC]) -> JS
    prepBranch (tag, code) =
      JSAlloc (
        translateName name ++ "$" ++ show tag
      ) (Just $ JSFunction ["vm", "oldbase", "myoldbase"] (
          JSSeq $ map (translateBC info) code
        )
      )

translateDecl info (name, bc) =
  [ JSAlloc (
       translateName name
     ) (Just $ JSFunction ["vm", "oldbase"] (
         JSSeq $ JSAlloc "myoldbase" Nothing : map (translateBC info)bc
       )
     )
  ]


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
translateConstant (BI i)                   = jsBigInt (JSString $ show i)
translateConstant (BI 0)                   = JSNum (JSInteger JSBigZero)
translateConstant (BI 1)                   = JSNum (JSInteger JSBigOne)
translateConstant (B8 b)                   = JSWord (JSWord8 b)
translateConstant (B16 b)                  = JSWord (JSWord16 b)
translateConstant (B32 b)                  = JSWord (JSWord32 b)
translateConstant (B64 b)                  = JSWord (JSWord64 b)
translateConstant c =
  JSError $ "Unimplemented Constant: " ++ show c


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

translateName :: Name -> String
translateName n = "_idris_" ++ concatMap cchar (showCG n)
  where cchar x | isAlpha x || isDigit x = [x]
                | otherwise = "_" ++ show (fromEnum x) ++ "_"

jsASSIGN :: CompileInfo -> Reg -> Reg -> JS
jsASSIGN _ r1 r2 = JSAssign (translateReg r1) (translateReg r2)

jsASSIGNCONST :: CompileInfo -> Reg -> Const -> JS
jsASSIGNCONST _ r c = JSAssign (translateReg r) (translateConstant c)

jsCALL :: CompileInfo -> Name -> JS
jsCALL _ n = JSApp (JSIdent (translateName n)) [JSIdent "vm", JSIdent "myoldbase"]

jsTAILCALL :: CompileInfo -> Name -> JS
jsTAILCALL _ n = JSApp (JSIdent (translateName n)) [JSIdent "vm", JSIdent "oldbase"]

jsFOREIGN :: CompileInfo -> Reg -> String -> [(FType, Reg)] -> JS
jsFOREIGN _ reg n args =
  JSAssign (
    translateReg reg
  ) (
    JSApp (JSIdent n) (map (translateReg . snd) args)
  )

jsREBASE :: CompileInfo -> JS
jsREBASE _ =
  JSAssign (
    JSProj (JSIdent "vm") "valstack_base"
  ) (
    JSIdent "oldbase"
  )

jsSTOREOLD :: CompileInfo ->JS
jsSTOREOLD _ =
  JSAssign (
    JSIdent "myoldbase"
  ) (
    JSProj (JSIdent "vm") "valstack_base"
  )

jsADDTOP :: CompileInfo -> Int -> JS
jsADDTOP info n
  | 0 <- n    = JSNoop
  | otherwise =
      JSBinOp "+=" (JSProj (JSIdent "vm") "valstack_top") (JSNum (JSInt n))

jsTOPBASE :: CompileInfo -> Int -> JS
jsTOPBASE info n
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

jsBASETOP :: CompileInfo -> Int -> JS
jsBASETOP info n
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

jsNULL :: CompileInfo -> Reg -> JS
jsNULL _ r = JSAssign (translateReg r) JSNull

jsERROR :: CompileInfo -> String -> JS
jsERROR _ = JSError

jsSLIDE :: CompileInfo -> Int -> JS
jsSLIDE _ n = JSApp (JSIdent "i$SLIDE") [JSIdent "vm", JSNum (JSInt n)]

jsMKCON :: CompileInfo -> Reg -> Int -> [Reg] -> JS
jsMKCON info r t rs =
  JSAssign (translateReg r) (
    JSNew "i$CON" [ JSNum (JSInt t)
                  , JSArray (map translateReg rs)
                  , if t `elem` compileInfoApplyCases info
                       then JSIdent $ translateName (sMN 0 "APPLY") ++ "$" ++ show t
                       else JSNull
                  ]
  )

jsInstanceOf :: JS -> String -> JS
jsInstanceOf obj cls = JSBinOp "instanceof" obj (JSIdent cls)

jsOr :: JS -> JS -> JS
jsOr lhs rhs = JSBinOp "||" lhs rhs

jsAnd :: JS -> JS -> JS
jsAnd lhs rhs = JSBinOp "&&" lhs rhs

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

jsCASE :: CompileInfo -> Bool -> Reg -> [(Int, [BC])] -> Maybe [BC] -> JS
jsCASE info safe reg cases def =
  JSSwitch (tag safe $ translateReg reg) (
    map ((JSNum . JSInt) *** prepBranch) cases
  ) (fmap prepBranch def)
    where
      tag :: Bool -> JS -> JS
      tag True  = jsCTAG
      tag False = jsTAG

      prepBranch :: [BC] -> JS
      prepBranch bc = JSSeq $ map (translateBC info) bc

      jsTAG :: JS -> JS
      jsTAG js =
        JSTernary (jsIsNumber js `jsOr` jsIsNull js) (
          JSNum (JSInt $ negate 1)
        ) (JSTernary (js `jsInstanceOf` "i$CON") (
            JSProj js "tag"
          ) (JSNum (JSInt $ negate 1)))

      jsCTAG :: JS -> JS
      jsCTAG js = JSProj js "tag"


jsCONSTCASE :: CompileInfo -> Reg -> [(Const, [BC])] -> Maybe [BC] -> JS
jsCONSTCASE info reg cases def =
  JSCond $ (
    map (jsEq (translateReg reg) . translateConstant *** prepBranch) cases
  ) ++ (maybe [] ((:[]) . ((,) JSNoop) . prepBranch) def)
    where
      prepBranch :: [BC] -> JS
      prepBranch bc = JSSeq $ map (translateBC info) bc

jsPROJECT :: CompileInfo -> Reg -> Int -> Int -> JS
jsPROJECT _ reg loc ar =
  JSApp (JSIdent "i$PROJECT") [ JSIdent "vm"
                              , translateReg reg
                              , JSNum (JSInt loc)
                              , JSNum (JSInt ar)
                              ]

jsOP :: CompileInfo -> Reg -> PrimFn -> [Reg] -> JS
jsOP _ reg op args = JSAssign (translateReg reg) jsOP'
  where
    jsOP' :: JS
    jsOP'
      | LNoOp <- op = translateReg (last args)

      | (LZExt (ITFixed IT8) ITNative)  <- op = jsUnPackBits $ translateReg (last args)
      | (LZExt (ITFixed IT16) ITNative) <- op = jsUnPackBits $ translateReg (last args)
      | (LZExt (ITFixed IT32) ITNative) <- op = jsUnPackBits $ translateReg (last args)

      | (LZExt _ ITBig)        <- op = jsBigInt $ JSApp  (JSIdent "String") [translateReg (last args)]
      | (LPlus (ATInt ITBig))  <- op
      , (lhs:rhs:_)            <- args = invokeMeth lhs "add" [rhs]
      | (LMinus (ATInt ITBig)) <- op
      , (lhs:rhs:_)            <- args = invokeMeth lhs "subtract" [rhs]
      | (LTimes (ATInt ITBig)) <- op
      , (lhs:rhs:_)            <- args = invokeMeth lhs "multiply" [rhs]
      | (LSDiv (ATInt ITBig))  <- op
      , (lhs:rhs:_)            <- args = invokeMeth lhs "divide" [rhs]
      | (LSRem (ATInt ITBig))  <- op
      , (lhs:rhs:_)            <- args = invokeMeth lhs "mod" [rhs]
      | (LEq (ATInt ITBig))    <- op
      , (lhs:rhs:_)            <- args = invokeMeth lhs "equals" [rhs]
      | (LSLt (ATInt ITBig))   <- op
      , (lhs:rhs:_)            <- args = invokeMeth lhs "lesser" [rhs]
      | (LSLe (ATInt ITBig))   <- op
      , (lhs:rhs:_)            <- args = invokeMeth lhs "lesserOrEquals" [rhs]
      | (LSGt (ATInt ITBig))   <- op
      , (lhs:rhs:_)            <- args = invokeMeth lhs "greater" [rhs]
      | (LSGe (ATInt ITBig))   <- op
      , (lhs:rhs:_)            <- args = invokeMeth lhs "greaterOrEquals" [rhs]

      | (LPlus ATFloat)  <- op
      , (lhs:rhs:_)      <- args = translateBinaryOp "+" lhs rhs
      | (LMinus ATFloat) <- op
      , (lhs:rhs:_)      <- args = translateBinaryOp "-" lhs rhs
      | (LTimes ATFloat) <- op
      , (lhs:rhs:_)      <- args = translateBinaryOp "*" lhs rhs
      | (LSDiv ATFloat)  <- op
      , (lhs:rhs:_)      <- args = translateBinaryOp "/" lhs rhs
      | (LEq ATFloat)    <- op
      , (lhs:rhs:_)      <- args = translateBinaryOp "==" lhs rhs
      | (LSLt ATFloat)   <- op
      , (lhs:rhs:_)      <- args = translateBinaryOp "<" lhs rhs
      | (LSLe ATFloat)   <- op
      , (lhs:rhs:_)      <- args = translateBinaryOp "<=" lhs rhs
      | (LSGt ATFloat)   <- op
      , (lhs:rhs:_)      <- args = translateBinaryOp ">" lhs rhs
      | (LSGe ATFloat)   <- op
      , (lhs:rhs:_)      <- args = translateBinaryOp ">=" lhs rhs

      | (LPlus (ATInt ITChar)) <- op
      , (lhs:rhs:_)            <- args =
          jsCall "__IDRRT__fromCharCode" [
            JSBinOp "+" (
              jsCall "__IDRRT__charCode" [translateReg lhs]
            ) (
              jsCall "__IDRRT__charCode" [translateReg rhs]
            )
          ]

      | (LTrunc (ITFixed IT16) (ITFixed IT8)) <- op
      , (arg:_)                               <- args =
          jsPackUBits8 (
            JSBinOp "&" (jsUnPackBits $ translateReg arg) (JSNum (JSInt 0xFF))
          )

      | (LTrunc (ITFixed IT32) (ITFixed IT16)) <- op
      , (arg:_)                                <- args =
          jsPackUBits16 (
            JSBinOp "&" (jsUnPackBits $ translateReg arg) (JSNum (JSInt 0xFFFF))
          )

      | (LTrunc (ITFixed IT64) (ITFixed IT32)) <- op
      , (arg:_)                                <- args =
          jsPackUBits32 (
            jsMeth (jsMeth (translateReg arg) "and" [
              jsBigInt (JSString $ show 0xFFFFFFFF)
            ]) "intValue" []
          )

      | (LTrunc ITBig (ITFixed IT64)) <- op
      , (arg:_)                       <- args =
          jsMeth (translateReg arg) "and" [
            jsBigInt (JSString $ show 0xFFFFFFFFFFFFFFFF)
          ]

      | (LLSHR (ITFixed IT8)) <- op
      , (lhs:rhs:_)           <- args =
          jsPackUBits8 (
            JSBinOp ">>" (jsUnPackBits $ translateReg lhs) (jsUnPackBits $ translateReg rhs)
          )

      | (LLSHR (ITFixed IT16)) <- op
      , (lhs:rhs:_)            <- args =
          jsPackUBits16 (
            JSBinOp ">>" (jsUnPackBits $ translateReg lhs) (jsUnPackBits $ translateReg rhs)
          )

      | (LLSHR (ITFixed IT32)) <- op
      , (lhs:rhs:_)            <- args =
          jsPackUBits32  (
            JSBinOp ">>" (jsUnPackBits $ translateReg lhs) (jsUnPackBits $ translateReg rhs)
          )

      | (LLSHR (ITFixed IT64)) <- op
      , (lhs:rhs:_)            <- args =
          jsMeth (translateReg lhs) "shiftRight" [translateReg rhs]

      | (LSHL (ITFixed IT8)) <- op
      , (lhs:rhs:_)          <- args =
          jsPackUBits8 (
            JSBinOp "<<" (jsUnPackBits $ translateReg lhs) (jsUnPackBits $ translateReg rhs)
          )

      | (LSHL (ITFixed IT16)) <- op
      , (lhs:rhs:_)           <- args =
          jsPackUBits16 (
            JSBinOp "<<" (jsUnPackBits $ translateReg lhs) (jsUnPackBits $ translateReg rhs)
          )

      | (LSHL (ITFixed IT32)) <- op
      , (lhs:rhs:_)           <- args =
          jsPackUBits32  (
            JSBinOp "<<" (jsUnPackBits $ translateReg lhs) (jsUnPackBits $ translateReg rhs)
          )

      | (LSHL (ITFixed IT64)) <- op
      , (lhs:rhs:_)           <- args =
          jsMeth (jsMeth (translateReg lhs) "shiftLeft" [translateReg rhs]) "and" [
            jsBigInt (JSString $ show 0xFFFFFFFFFFFFFFFF)
          ]

      | (LAnd (ITFixed IT8)) <- op
      , (lhs:rhs:_)          <- args =
          jsPackUBits8 (
            JSBinOp "&" (jsUnPackBits (translateReg lhs)) (jsUnPackBits (translateReg rhs))
          )

      | (LAnd (ITFixed IT16)) <- op
      , (lhs:rhs:_)           <- args =
          jsPackUBits16 (
            JSBinOp "&" (jsUnPackBits (translateReg lhs)) (jsUnPackBits (translateReg rhs))
          )

      | (LAnd (ITFixed IT32)) <- op
      , (lhs:rhs:_)           <- args =
          jsPackUBits32 (
            JSBinOp "&" (jsUnPackBits (translateReg lhs)) (jsUnPackBits (translateReg rhs))
          )

      | (LAnd (ITFixed IT64)) <- op
      , (lhs:rhs:_)           <- args =
          jsMeth (translateReg lhs) "and" [translateReg rhs]

      | (LOr (ITFixed IT8)) <- op
      , (lhs:rhs:_)         <- args =
          jsPackUBits8 (
            JSBinOp "|" (jsUnPackBits (translateReg lhs)) (jsUnPackBits (translateReg rhs))
          )

      | (LOr (ITFixed IT16)) <- op
      , (lhs:rhs:_)          <- args =
          jsPackUBits16 (
            JSBinOp "|" (jsUnPackBits (translateReg lhs)) (jsUnPackBits (translateReg rhs))
          )

      | (LOr (ITFixed IT32)) <- op
      , (lhs:rhs:_)          <- args =
          jsPackUBits32 (
            JSBinOp "|" (jsUnPackBits (translateReg lhs)) (jsUnPackBits (translateReg rhs))
          )

      | (LOr (ITFixed IT64)) <- op
      , (lhs:rhs:_)          <- args =
          jsMeth (translateReg lhs) "or" [translateReg rhs]

      | (LXOr (ITFixed IT8)) <- op
      , (lhs:rhs:_)          <- args =
          jsPackUBits8 (
            JSBinOp "^" (jsUnPackBits (translateReg lhs)) (jsUnPackBits (translateReg rhs))
          )

      | (LXOr (ITFixed IT16)) <- op
      , (lhs:rhs:_)           <- args =
          jsPackUBits16 (
            JSBinOp "^" (jsUnPackBits (translateReg lhs)) (jsUnPackBits (translateReg rhs))
          )

      | (LXOr (ITFixed IT32)) <- op
      , (lhs:rhs:_)           <- args =
          jsPackUBits32 (
            JSBinOp "^" (jsUnPackBits (translateReg lhs)) (jsUnPackBits (translateReg rhs))
          )

      | (LXOr (ITFixed IT64)) <- op
      , (lhs:rhs:_)           <- args =
          jsMeth (translateReg lhs) "xor" [translateReg rhs]

      | (LPlus (ATInt (ITFixed IT8))) <- op
      , (lhs:rhs:_)                   <- args =
          jsPackUBits8 (
            JSBinOp "+" (jsUnPackBits (translateReg lhs)) (jsUnPackBits (translateReg rhs))
          )

      | (LPlus (ATInt (ITFixed IT16))) <- op
      , (lhs:rhs:_)                    <- args =
          jsPackUBits16 (
            JSBinOp "+" (jsUnPackBits (translateReg lhs)) (jsUnPackBits (translateReg rhs))
          )

      | (LPlus (ATInt (ITFixed IT32))) <- op
      , (lhs:rhs:_)                    <- args =
          jsPackUBits32 (
            JSBinOp "+" (jsUnPackBits (translateReg lhs)) (jsUnPackBits (translateReg rhs))
          )

      | (LPlus (ATInt (ITFixed IT64))) <- op
      , (lhs:rhs:_)                    <- args =
          jsMeth (jsMeth (translateReg lhs) "add" [translateReg rhs]) "and" [
            jsBigInt (JSString $ show 0xFFFFFFFFFFFFFFFF)
          ]

      | (LMinus (ATInt (ITFixed IT8))) <- op
      , (lhs:rhs:_)                    <- args =
          jsPackUBits8 (
            JSBinOp "-" (jsUnPackBits (translateReg lhs)) (jsUnPackBits (translateReg rhs))
          )

      | (LMinus (ATInt (ITFixed IT16))) <- op
      , (lhs:rhs:_)                     <- args =
          jsPackUBits16 (
            JSBinOp "-" (jsUnPackBits (translateReg lhs)) (jsUnPackBits (translateReg rhs))
          )

      | (LMinus (ATInt (ITFixed IT32))) <- op
      , (lhs:rhs:_)                     <- args =
          jsPackUBits32 (
            JSBinOp "-" (jsUnPackBits (translateReg lhs)) (jsUnPackBits (translateReg rhs))
          )

      | (LMinus (ATInt (ITFixed IT64))) <- op
      , (lhs:rhs:_)                     <- args =
          jsMeth (jsMeth (translateReg lhs) "subtract" [translateReg rhs]) "and" [
            jsBigInt (JSString $ show 0xFFFFFFFFFFFFFFFF)
          ]

      | (LTimes (ATInt (ITFixed IT8))) <- op
      , (lhs:rhs:_)                    <- args =
          jsPackUBits8 (
            JSBinOp "*" (jsUnPackBits (translateReg lhs)) (jsUnPackBits (translateReg rhs))
          )

      | (LTimes (ATInt (ITFixed IT16))) <- op
      , (lhs:rhs:_)                     <- args =
          jsPackUBits16 (
            JSBinOp "*" (jsUnPackBits (translateReg lhs)) (jsUnPackBits (translateReg rhs))
          )

      | (LTimes (ATInt (ITFixed IT32))) <- op
      , (lhs:rhs:_)                     <- args =
          jsPackUBits32 (
            JSBinOp "*" (jsUnPackBits (translateReg lhs)) (jsUnPackBits (translateReg rhs))
          )

      | (LTimes (ATInt (ITFixed IT64))) <- op
      , (lhs:rhs:_)                     <- args =
          jsMeth (jsMeth (translateReg lhs) "multiply" [translateReg rhs]) "and" [
            jsBigInt (JSString $ show 0xFFFFFFFFFFFFFFFF)
          ]

      | (LEq (ATInt (ITFixed IT8))) <- op
      , (lhs:rhs:_)                 <- args =
          jsPackUBits8 (
            JSBinOp "==" (jsUnPackBits (translateReg lhs)) (jsUnPackBits (translateReg rhs))
          )

      | (LEq (ATInt (ITFixed IT16))) <- op
      , (lhs:rhs:_)                  <- args =
          jsPackUBits16 (
            JSBinOp "==" (jsUnPackBits (translateReg lhs)) (jsUnPackBits (translateReg rhs))
          )

      | (LEq (ATInt (ITFixed IT32))) <- op
      , (lhs:rhs:_)                  <- args =
          jsPackUBits32 (
            JSBinOp "==" (jsUnPackBits (translateReg lhs)) (jsUnPackBits (translateReg rhs))
          )

      | (LEq (ATInt (ITFixed IT64))) <- op
      , (lhs:rhs:_)                   <- args =
          jsMeth (jsMeth (translateReg lhs) "equals" [translateReg rhs]) "and" [
            jsBigInt (JSString $ show 0xFFFFFFFFFFFFFFFF)
          ]

      | (LLt (ITFixed IT8)) <- op
      , (lhs:rhs:_)         <- args =
          jsPackUBits8 (
            JSBinOp "<" (jsUnPackBits (translateReg lhs)) (jsUnPackBits (translateReg rhs))
          )

      | (LLt (ITFixed IT16)) <- op
      , (lhs:rhs:_)          <- args =
          jsPackUBits16 (
            JSBinOp "<" (jsUnPackBits (translateReg lhs)) (jsUnPackBits (translateReg rhs))
          )

      | (LLt (ITFixed IT32)) <- op
      , (lhs:rhs:_)          <- args =
          jsPackUBits32 (
            JSBinOp "<" (jsUnPackBits (translateReg lhs)) (jsUnPackBits (translateReg rhs))
          )

      | (LLt (ITFixed IT64)) <- op
      , (lhs:rhs:_)          <- args = invokeMeth lhs "lesser" [rhs]

      | (LLe (ITFixed IT8)) <- op
      , (lhs:rhs:_)         <- args =
          jsPackUBits8 (
            JSBinOp "<=" (jsUnPackBits (translateReg lhs)) (jsUnPackBits (translateReg rhs))
          )

      | (LLe (ITFixed IT16)) <- op
      , (lhs:rhs:_)          <- args =
          jsPackUBits16 (
            JSBinOp "<=" (jsUnPackBits (translateReg lhs)) (jsUnPackBits (translateReg rhs))
          )

      | (LLe (ITFixed IT32)) <- op
      , (lhs:rhs:_)          <- args =
          jsPackUBits32 (
            JSBinOp "<=" (jsUnPackBits (translateReg lhs)) (jsUnPackBits (translateReg rhs))
          )

      | (LLe (ITFixed IT64)) <- op
      , (lhs:rhs:_)          <- args = invokeMeth lhs "lesserOrEquals" [rhs]

      | (LGt (ITFixed IT8)) <- op
      , (lhs:rhs:_)         <- args =
          jsPackUBits8 (
            JSBinOp ">" (jsUnPackBits (translateReg lhs)) (jsUnPackBits (translateReg rhs))
          )

      | (LGt (ITFixed IT16)) <- op
      , (lhs:rhs:_)          <- args =
          jsPackUBits16 (
            JSBinOp ">" (jsUnPackBits (translateReg lhs)) (jsUnPackBits (translateReg rhs))
          )
      | (LGt (ITFixed IT32)) <- op
      , (lhs:rhs:_)          <- args =
          jsPackUBits32 (
            JSBinOp ">" (jsUnPackBits (translateReg lhs)) (jsUnPackBits (translateReg rhs))
          )

      | (LGt (ITFixed IT64)) <- op
      , (lhs:rhs:_)          <- args = invokeMeth lhs "greater" [rhs]

      | (LGe (ITFixed IT8)) <- op
      , (lhs:rhs:_)         <- args =
          jsPackUBits8 (
            JSBinOp ">=" (jsUnPackBits (translateReg lhs)) (jsUnPackBits (translateReg rhs))
          )

      | (LGe (ITFixed IT16)) <- op
      , (lhs:rhs:_)          <- args =
          jsPackUBits16 (
            JSBinOp ">=" (jsUnPackBits (translateReg lhs)) (jsUnPackBits (translateReg rhs))
          )
      | (LGe (ITFixed IT32)) <- op
      , (lhs:rhs:_)          <- args =
          jsPackUBits32 (
            JSBinOp ">=" (jsUnPackBits (translateReg lhs)) (jsUnPackBits (translateReg rhs))
          )

      | (LGe (ITFixed IT64)) <- op
      , (lhs:rhs:_)          <- args = invokeMeth lhs "greaterOrEquals" [rhs]

      | (LUDiv (ITFixed IT8)) <- op
      , (lhs:rhs:_)           <- args =
          jsPackUBits8 (
            JSBinOp "/" (jsUnPackBits (translateReg lhs)) (jsUnPackBits (translateReg rhs))
          )

      | (LUDiv (ITFixed IT16)) <- op
      , (lhs:rhs:_)            <- args =
          jsPackUBits16 (
            JSBinOp "/" (jsUnPackBits (translateReg lhs)) (jsUnPackBits (translateReg rhs))
          )

      | (LUDiv (ITFixed IT32)) <- op
      , (lhs:rhs:_)            <- args =
          jsPackUBits32 (
            JSBinOp "/" (jsUnPackBits (translateReg lhs)) (jsUnPackBits (translateReg rhs))
          )

      | (LUDiv (ITFixed IT64)) <- op
      , (lhs:rhs:_)            <- args = invokeMeth lhs "divide" [rhs]

      | (LSDiv (ATInt (ITFixed IT8))) <- op
      , (lhs:rhs:_)                   <- args =
          jsPackSBits8 (
            JSBinOp "/" (
              jsUnPackBits $ jsPackSBits8 $ jsUnPackBits (translateReg lhs)
            ) (
              jsUnPackBits $ jsPackSBits8 $ jsUnPackBits (translateReg rhs)
            )
          )

      | (LSDiv (ATInt (ITFixed IT16))) <- op
      , (lhs:rhs:_)                    <- args =
          jsPackSBits16 (
            JSBinOp "/" (
              jsUnPackBits $ jsPackSBits16 $ jsUnPackBits (translateReg lhs)
            ) (
              jsUnPackBits $ jsPackSBits16 $ jsUnPackBits (translateReg rhs)
            )
          )

      | (LSDiv (ATInt (ITFixed IT32))) <- op
      , (lhs:rhs:_)                    <- args =
          jsPackSBits32 (
            JSBinOp "/" (
              jsUnPackBits $ jsPackSBits32 $ jsUnPackBits (translateReg lhs)
            ) (
              jsUnPackBits $ jsPackSBits32 $ jsUnPackBits (translateReg rhs)
            )
          )

      | (LSDiv (ATInt (ITFixed IT64))) <- op
      , (lhs:rhs:_)                    <- args = invokeMeth lhs "divide" [rhs]

      | (LSRem (ATInt (ITFixed IT8))) <- op
      , (lhs:rhs:_)                   <- args =
          jsPackSBits8 (
            JSBinOp "%" (
              jsUnPackBits $ jsPackSBits8 $ jsUnPackBits (translateReg lhs)
            ) (
              jsUnPackBits $ jsPackSBits8 $ jsUnPackBits (translateReg rhs)
            )
          )

      | (LSRem (ATInt (ITFixed IT16))) <- op
      , (lhs:rhs:_)                    <- args =
          jsPackSBits16 (
            JSBinOp "%" (
              jsUnPackBits $ jsPackSBits16 $ jsUnPackBits (translateReg lhs)
            ) (
              jsUnPackBits $ jsPackSBits16 $ jsUnPackBits (translateReg rhs)
            )
          )

      | (LSRem (ATInt (ITFixed IT32))) <- op
      , (lhs:rhs:_)                    <- args =
          jsPackSBits32 (
            JSBinOp "%" (
              jsUnPackBits $ jsPackSBits32 $ jsUnPackBits (translateReg lhs)
            ) (
              jsUnPackBits $ jsPackSBits32 $ jsUnPackBits (translateReg rhs)
            )
          )

      | (LSRem (ATInt (ITFixed IT64))) <- op
      , (lhs:rhs:_)                    <- args = invokeMeth lhs "mod" [rhs]

      | (LCompl (ITFixed IT8)) <- op
      , (arg:_)                <- args =
          jsPackSBits8 $ JSPreOp "~" $ jsUnPackBits (translateReg arg)

      | (LCompl (ITFixed IT16)) <- op
      , (arg:_)                 <- args =
          jsPackSBits16 $ JSPreOp "~" $ jsUnPackBits (translateReg arg)

      | (LCompl (ITFixed IT32)) <- op
      , (arg:_)                 <- args =
          jsPackSBits32 $ JSPreOp "~" $ jsUnPackBits (translateReg arg)

      | (LCompl (ITFixed IT64)) <- op
      , (arg:_)     <- args =
          invokeMeth arg "not" []

      | (LPlus _)   <- op
      , (lhs:rhs:_) <- args = translateBinaryOp "+" lhs rhs
      | (LMinus _)  <- op
      , (lhs:rhs:_) <- args = translateBinaryOp "-" lhs rhs
      | (LTimes _)  <- op
      , (lhs:rhs:_) <- args = translateBinaryOp "*" lhs rhs
      | (LSDiv _)   <- op
      , (lhs:rhs:_) <- args = translateBinaryOp "/" lhs rhs
      | (LSRem _)   <- op
      , (lhs:rhs:_) <- args = translateBinaryOp "%" lhs rhs
      | (LEq _)     <- op
      , (lhs:rhs:_) <- args = translateBinaryOp "==" lhs rhs
      | (LSLt _)    <- op
      , (lhs:rhs:_) <- args = translateBinaryOp "<" lhs rhs
      | (LSLe _)    <- op
      , (lhs:rhs:_) <- args = translateBinaryOp "<=" lhs rhs
      | (LSGt _)    <- op
      , (lhs:rhs:_) <- args = translateBinaryOp ">" lhs rhs
      | (LSGe _)    <- op
      , (lhs:rhs:_) <- args = translateBinaryOp ">=" lhs rhs
      | (LAnd _)    <- op
      , (lhs:rhs:_) <- args = translateBinaryOp "&" lhs rhs
      | (LOr _)     <- op
      , (lhs:rhs:_) <- args = translateBinaryOp "|" lhs rhs
      | (LXOr _)    <- op
      , (lhs:rhs:_) <- args = translateBinaryOp "^" lhs rhs
      | (LSHL _)    <- op
      , (lhs:rhs:_) <- args = translateBinaryOp "<<" rhs lhs
      | (LASHR _)   <- op
      , (lhs:rhs:_) <- args = translateBinaryOp ">>" rhs lhs
      | (LCompl _)  <- op
      , (arg:_)     <- args = JSPreOp "~" (translateReg arg)

      | LStrConcat  <- op
      , (lhs:rhs:_) <- args = translateBinaryOp "+" lhs rhs
      | LStrEq      <- op
      , (lhs:rhs:_) <- args = translateBinaryOp "==" lhs rhs
      | LStrLt      <- op
      , (lhs:rhs:_) <- args = translateBinaryOp "<" lhs rhs
      | LStrLen     <- op
      , (arg:_)     <- args = JSProj (translateReg arg) "length"
      | (LStrInt ITNative)      <- op
      , (arg:_)                 <- args = jsCall "parseInt" [translateReg arg]
      | (LIntStr ITNative)      <- op
      , (arg:_)                 <- args = jsCall "String" [translateReg arg]
      | (LSExt ITNative ITBig)  <- op
      , (arg:_)                 <- args = jsBigInt $ jsCall "String" [translateReg arg]
      | (LTrunc ITBig ITNative) <- op
      , (arg:_)                 <- args = jsMeth (translateReg arg) "intValue" []
      | (LIntStr ITBig)         <- op
      , (arg:_)                 <- args = jsMeth (translateReg arg) "toString" []
      | (LStrInt ITBig)         <- op
      , (arg:_)                 <- args = jsBigInt $ translateReg arg
      | LFloatStr               <- op
      , (arg:_)                 <- args = jsCall "String" [translateReg arg]
      | LStrFloat               <- op
      , (arg:_)                 <- args = jsCall "parseFloat" [translateReg arg]
      | (LIntFloat ITNative)    <- op
      , (arg:_)                 <- args = translateReg arg
      | (LFloatInt ITNative)    <- op
      , (arg:_)                 <- args = translateReg arg
      | (LChInt ITNative)       <- op
      , (arg:_)                 <- args = jsCall "__IDRRT__charCode" [translateReg arg]
      | (LIntCh ITNative)       <- op
      , (arg:_)                 <- args = jsCall "__IDRRT__fromCharCode" [translateReg arg]

      | LFExp       <- op
      , (arg:_)     <- args = jsCall "Math.exp" [translateReg arg]
      | LFLog       <- op
      , (arg:_)     <- args = jsCall "Math.log" [translateReg arg]
      | LFSin       <- op
      , (arg:_)     <- args = jsCall "Math.sin" [translateReg arg]
      | LFCos       <- op
      , (arg:_)     <- args = jsCall "Math.cos" [translateReg arg]
      | LFTan       <- op
      , (arg:_)     <- args = jsCall "Math.tan" [translateReg arg]
      | LFASin      <- op
      , (arg:_)     <- args = jsCall "Math.asin" [translateReg arg]
      | LFACos      <- op
      , (arg:_)     <- args = jsCall "Math.acos" [translateReg arg]
      | LFATan      <- op
      , (arg:_)     <- args = jsCall "Math.atan" [translateReg arg]
      | LFSqrt      <- op
      , (arg:_)     <- args = jsCall "Math.sqrt" [translateReg arg]
      | LFFloor     <- op
      , (arg:_)     <- args = jsCall "Math.floor" [translateReg arg]
      | LFCeil      <- op
      , (arg:_)     <- args = jsCall "Math.ceil" [translateReg arg]

      | LStrCons    <- op
      , (lhs:rhs:_) <- args = invokeMeth lhs "concat" [rhs]
      | LStrHead    <- op
      , (arg:_)     <- args = JSIndex (translateReg arg) (JSNum (JSInt 0))
      | LStrRev     <- op
      , (arg:_)     <- args = JSProj (translateReg arg) "split('').reverse().join('')"
      | LStrIndex   <- op
      , (lhs:rhs:_) <- args = JSIndex (translateReg lhs) (translateReg rhs)
      | LStrTail    <- op
      , (arg:_)     <- args =
          let v = translateReg arg in
              JSApp (JSProj v "substr") [
                JSNum (JSInt 1),
                JSBinOp "-" (JSProj v "length") (JSNum (JSInt 1))
              ]

      | LSystemInfo <- op
      , (arg:_) <- args = jsCall "__IDRRT__systemInfo"  [translateReg arg]
      | LNullPtr    <- op
      , (_)         <- args = JSNull
      | otherwise = JSError $ "Not implemented: " ++ show op
        where
          translateBinaryOp :: String -> Reg -> Reg -> JS
          translateBinaryOp op lhs rhs =
            JSBinOp op (translateReg lhs) (translateReg rhs)

          invokeMeth :: Reg -> String -> [Reg] -> JS
          invokeMeth obj meth args =
            JSApp (JSProj (translateReg obj) meth) $ map translateReg args

          jsMeth :: JS -> String -> [JS] -> JS
          jsMeth obj meth args = JSApp (JSProj obj meth) args


          jsCall :: String -> [JS] -> JS
          jsCall fun args = JSApp (JSIdent fun) args

jsRESERVE :: CompileInfo -> Int -> JS
jsRESERVE _ _ = JSNoop

translateBC :: CompileInfo -> BC -> JS
translateBC info bc
  | ASSIGN r1 r2          <- bc = jsASSIGN info r1 r2
  | ASSIGNCONST r c       <- bc = jsASSIGNCONST info r c
  | UPDATE r1 r2          <- bc = jsASSIGN info r1 r2
  | ADDTOP n              <- bc = jsADDTOP info n
  | NULL r                <- bc = jsNULL info r
  | CALL n                <- bc = jsCALL info n
  | TAILCALL n            <- bc = jsTAILCALL info n
  | FOREIGNCALL r _ _ n a <- bc = jsFOREIGN info r n a
  | TOPBASE n             <- bc = jsTOPBASE info n
  | BASETOP n             <- bc = jsBASETOP info n
  | STOREOLD              <- bc = jsSTOREOLD info
  | SLIDE n               <- bc = jsSLIDE info n
  | REBASE                <- bc = jsREBASE info
  | RESERVE n             <- bc = jsRESERVE info n
  | MKCON r t rs          <- bc = jsMKCON info r t rs
  | CASE s r c d          <- bc = jsCASE info s r c d
  | CONSTCASE r c d       <- bc = jsCONSTCASE info r c d
  | PROJECT r l a         <- bc = jsPROJECT info r l a
  | OP r o a              <- bc = jsOP info r o a
  | ERROR e               <- bc = jsERROR info e
  | otherwise                   = JSRaw $ show bc
  {-| PROJECTINTO _ _ _     <- bc = undefined-}

