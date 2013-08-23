{-# LANGUAGE PatternGuards #-}

module IRTS.CodegenJavaScript (codegenJavaScript, JSTarget(..)) where

import Idris.AbsSyntax hiding (TypeCase)
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
import Data.Maybe
import System.IO
import System.Directory

idrNamespace :: String
idrNamespace   = "__IDR__"
idrRTNamespace = "__IDRRT__"
idrLTNamespace = "__IDRLT__"

data JSTarget = Node | JavaScript deriving Eq

data JSType = JSIntTy
            | JSStringTy
            | JSIntegerTy
            | JSFloatTy
            | JSCharTy
            | JSPtrTy
            | JSForgotTy
            deriving Eq

data JSNum = JSInt Int
           | JSFloat Double
           | JSInteger Integer

data JS = JSRaw String
        | JSFunction [String] JS
        | JSType JSType
        | JSSeq [JS]
        | JSReturn JS
        | JSApp JS [JS]
        | JSNew String [JS]
        | JSError String
        | JSOp String JS JS
        | JSProj JS String
        | JSVar LVar
        | JSNull
        | JSThis
        | JSTrue
        | JSArray [JS]
        | JSObject [(String, JS)]
        | JSString String
        | JSNum JSNum
        | JSAssign JS JS
        | JSAlloc String (Maybe JS)
        | JSIndex JS JS
        | JSCond [(JS, JS)]

compileJS :: JS -> String
compileJS (JSRaw code) =
  code

compileJS (JSFunction args body) =
     "function("
   ++ intercalate "," args
   ++ "){\n"
   ++ compileJS body
   ++ "\n}"

compileJS (JSType ty)
  | JSIntTy     <- ty = idrRTNamespace ++ "Int"
  | JSStringTy  <- ty = idrRTNamespace ++ "String"
  | JSIntegerTy <- ty = idrRTNamespace ++ "Integer"
  | JSFloatTy   <- ty = idrRTNamespace ++ "Float"
  | JSCharTy    <- ty = idrRTNamespace ++ "Char"
  | JSPtrTy     <- ty = idrRTNamespace ++ "Ptr"
  | JSForgotTy  <- ty = idrRTNamespace ++ "Forgot"

compileJS (JSSeq seq) =
  intercalate ";\n" (map compileJS seq)

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
  "(function(){throw '" ++ exc ++ "';})()"

compileJS (JSOp op lhs rhs) =
  compileJS lhs ++ " " ++ op ++ " " ++ compileJS rhs

compileJS (JSProj obj field)
  | JSFunction {} <- obj =
    concat ["(", compileJS obj, ").", field]
  | otherwise =
    compileJS obj ++ '.' : field

compileJS (JSVar var) =
  translateVariableName var

compileJS JSNull =
  "null"

compileJS JSThis =
  "this"

compileJS JSTrue =
  "true"

compileJS (JSArray elems) =
  "[" ++ intercalate "," (map compileJS elems) ++ "]"

compileJS (JSObject fields) =
  "{" ++ intercalate ",\n" (map compileField fields) ++ "}"
  where
    compileField :: (String, JS) -> String
    compileField (name, val) = '\'' : name ++ "' : "  ++ compileJS val

compileJS (JSString str) =
  show str

compileJS (JSNum num)
  | JSInt i     <- num = show i
  | JSFloat f   <- num = show f
  | JSInteger i <- num = show i

compileJS (JSAssign lhs rhs) =
  compileJS lhs ++ "=" ++ compileJS rhs

compileJS (JSAlloc name val) =
  "var " ++ name ++ maybe "" ((" = " ++) . compileJS) val

compileJS (JSIndex lhs rhs) =
  compileJS lhs ++ "[" ++ compileJS rhs ++ "]"

compileJS (JSCond branches) =
  intercalate " else " $ map createIfBlock branches
  where
    createIfBlock (cond, e) =
         "if (" ++ compileJS cond ++") {\n"
      ++ "return " ++ compileJS e
      ++ ";\n}"

jsTailcall :: JS -> JS
jsTailcall call =
  jsCall (idrRTNamespace ++ "tailcall") [
    JSFunction [] (JSReturn call)
  ]

jsCall :: String -> [JS] -> JS
jsCall fun = JSApp (JSRaw fun)

jsMeth :: JS -> String -> [JS] -> JS
jsMeth obj meth =
  JSApp (JSProj obj meth)

jsInstanceOf :: JS -> JS -> JS
jsInstanceOf = JSOp "instanceof"

jsEq :: JS -> JS -> JS
jsEq = JSOp "=="

jsAnd :: JS -> JS -> JS
jsAnd = JSOp "&&"

jsType :: JS
jsType = JSRaw $ idrRTNamespace ++ "Type"

jsCon :: JS
jsCon = JSRaw $ idrRTNamespace ++ "Con"

jsTag :: JS -> JS
jsTag obj = JSProj obj "tag"

jsTypeTag :: JS -> JS
jsTypeTag obj = JSProj obj "type"

jsBigInt :: JS -> JS
jsBigInt val =
  JSApp (JSRaw $ idrRTNamespace ++ "bigInt") [val]

jsVar :: Int -> String
jsVar = ("__var_" ++) . show

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
  writeFile filename $ intercalate "\n" $ [ header
                                          , idrRuntime
                                          , tgtRuntime
                                          ] ++ functions ++ [mainLoop]

  setPermissions filename (emptyPermissions { readable   = True
                                            , executable = target == Node
                                            , writable   = True
                                            })
  where
    def :: [(String, SDecl)]
    def = map (first translateNamespace) definitions

    functions :: [String]
    functions = map (compileJS . translateDeclaration) def

    mainLoop :: String
    mainLoop = compileJS $
      JSSeq [ JSAlloc "main" $ Just $ JSFunction [] (
                jsTailcall $ jsCall "__IDR__runMain0" []
              )
            , jsCall "main" []
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

translateNamespace :: Name -> String
translateNamespace (UN _)    = idrNamespace
translateNamespace (NS _ ns) = idrNamespace ++ concatMap translateIdentifier ns
translateNamespace (MN _ _)  = idrNamespace

translateName :: Name -> String
translateName (UN name)   = translateIdentifier name
translateName (NS name _) = translateName name
translateName (MN i name) = translateIdentifier name ++ show i

translateConstant :: Const -> JS
translateConstant (I i)                    = JSNum (JSInt i)
translateConstant (Fl f)                   = JSNum (JSFloat f)
translateConstant (Ch c)                   = JSString [c]
translateConstant (Str s)                  = JSString s
translateConstant (AType (ATInt ITNative)) = JSType JSIntTy
translateConstant StrType                  = JSType JSStringTy
translateConstant (AType (ATInt ITBig))    = JSType JSIntegerTy
translateConstant (AType ATFloat)          = JSType JSFloatTy
translateConstant (AType (ATInt ITChar))   = JSType JSCharTy
translateConstant PtrType                  = JSType JSPtrTy
translateConstant Forgot                   = JSType JSForgotTy
translateConstant (BI i)                   = jsBigInt $ JSNum (JSInteger i)
translateConstant c =
  JSError $ "Unimplemented Constant: " ++ show c

translateDeclaration :: (String, SDecl) -> JS
translateDeclaration (path, SFun name params stackSize body)
  | (MN _ "APPLY") <- name =
    let fun = translateExpression body in
        jsDecl $ jsFun fun
  | (MN _ "EVAL")        <- name
  , (SChkCase var cases) <- body =
    let fun  = translateExpression body in
        JSSeq [ lookupTable var cases
              , jsDecl $ JSRaw $ concat [ "function(arg0){"
                                        , "if (arg0 instanceof __IDRRT__Con "
                                        , " && " ++ lookupTableName ++ ".hasOwnProperty(arg0.tag))"
                                        , "return " ++ lookupTableName ++ "[arg0.tag](arg0);"
                                        , "else "
                                        , "return arg0; }"
                                        ]
              ]
  | otherwise =
    let fun = translateExpression body in
        jsDecl $ jsFun fun

  where
    caseFun :: LVar -> SAlt -> JS
    caseFun var cse =
      jsFun (translateCase (Just (translateVariableName var)) cse)

    getTag :: SAlt -> Maybe String
    getTag (SConCase _ tag _ _ _) = Just $ show tag
    getTag _                      = Nothing

    lookupTableName :: String
    lookupTableName = idrLTNamespace ++ translateName name

    lookupTable :: LVar -> [SAlt] -> JS
    lookupTable var cases =
      JSAlloc lookupTableName $ Just (
        JSObject $ catMaybes $ map (lookupEntry var) cases
      )
      where
        lookupEntry :: LVar -> SAlt -> Maybe (String, JS)
        lookupEntry var alt = do
          tag <- getTag alt
          return (tag, caseFun var alt)

    jsDecl :: JS -> JS
    jsDecl = JSAlloc (path ++ translateName name) . Just

    jsFun :: JS -> JS
    jsFun body =
      JSFunction p (
        JSSeq $
        zipWith assignVar [0..] p ++
        map allocVar [numP .. (numP + stackSize - 1)] ++
        [JSReturn body]
      )
      where
        numP :: Int
        numP = length params

        allocVar :: Int -> JS
        allocVar n = JSAlloc (jsVar n) Nothing

        assignVar :: Int -> String -> JS
        assignVar n s = JSAlloc (jsVar n)  (Just $ JSRaw s)

        p :: [String]
        p = map translateName params

translateVariableName :: LVar -> String
translateVariableName (Loc i) =
  jsVar i

translateExpression :: SExp -> JS
translateExpression (SLet name value body) =
     JSApp (
        JSFunction [translateVariableName name] (
          JSReturn $ translateExpression body
        )
      ) [translateExpression value]

translateExpression (SConst cst) =
  translateConstant cst

translateExpression (SV var) =
  JSVar var

translateExpression (SApp tc name vars)
  | False <- tc =
    jsTailcall $ translateFunctionCall name vars
  | True <- tc =
    JSNew (idrRTNamespace ++ "Tailcall") [JSFunction [] (
      JSReturn $ translateFunctionCall name vars
    )]
  where
    translateFunctionCall name vars =
      jsCall (translateNamespace name ++ translateName name) (map JSVar vars)

translateExpression (SOp op vars)
  | LNoOp <- op = JSVar (last vars)

  | (LZExt _ ITBig)        <- op = jsBigInt $ JSVar (last vars)
  | (LPlus (ATInt ITBig))  <- op
  , (lhs:rhs:_)            <- vars = invokeMeth lhs "add" [rhs]
  | (LMinus (ATInt ITBig)) <- op
  , (lhs:rhs:_)            <- vars = invokeMeth lhs "minus" [rhs]
  | (LTimes (ATInt ITBig)) <- op
  , (lhs:rhs:_)            <- vars = invokeMeth lhs "times" [rhs]
  | (LSDiv (ATInt ITBig))  <- op
  , (lhs:rhs:_)            <- vars = invokeMeth lhs "divide" [rhs]
  | (LSRem (ATInt ITBig))  <- op
  , (lhs:rhs:_)            <- vars = invokeMeth lhs "mod" [rhs]
  | (LEq (ATInt ITBig))    <- op
  , (lhs:rhs:_)            <- vars = invokeMeth lhs "equals" [rhs]
  | (LSLt (ATInt ITBig))   <- op
  , (lhs:rhs:_)            <- vars = invokeMeth lhs "lesser" [rhs]
  | (LSLe (ATInt ITBig))   <- op
  , (lhs:rhs:_)            <- vars = invokeMeth lhs "lesserOrEquals" [rhs]
  | (LSGt (ATInt ITBig))   <- op
  , (lhs:rhs:_)            <- vars = invokeMeth lhs "greater" [rhs]
  | (LSGe (ATInt ITBig))   <- op
  , (lhs:rhs:_)            <- vars = invokeMeth lhs "greaterOrEquals" [rhs]

  | (LPlus ATFloat)  <- op
  , (lhs:rhs:_)      <- vars = translateBinaryOp "+" lhs rhs
  | (LMinus ATFloat) <- op
  , (lhs:rhs:_)      <- vars = translateBinaryOp "-" lhs rhs
  | (LTimes ATFloat) <- op
  , (lhs:rhs:_)      <- vars = translateBinaryOp "*" lhs rhs
  | (LSDiv ATFloat)  <- op
  , (lhs:rhs:_)      <- vars = translateBinaryOp "/" lhs rhs
  | (LEq ATFloat)    <- op
  , (lhs:rhs:_)      <- vars = translateBinaryOp "==" lhs rhs
  | (LSLt ATFloat)   <- op
  , (lhs:rhs:_)      <- vars = translateBinaryOp "<" lhs rhs
  | (LSLe ATFloat)   <- op
  , (lhs:rhs:_)      <- vars = translateBinaryOp "<=" lhs rhs
  | (LSGt ATFloat)   <- op
  , (lhs:rhs:_)      <- vars = translateBinaryOp ">" lhs rhs
  | (LSGe ATFloat)   <- op
  , (lhs:rhs:_)      <- vars = translateBinaryOp ">=" lhs rhs

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
  | (LSLt _)    <- op
  , (lhs:rhs:_) <- vars = translateBinaryOp "<" lhs rhs
  | (LSLe _)    <- op
  , (lhs:rhs:_) <- vars = translateBinaryOp "<=" lhs rhs
  | (LSGt _)    <- op
  , (lhs:rhs:_) <- vars = translateBinaryOp ">" lhs rhs
  | (LSGe _)    <- op
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
  , (arg:_)     <- vars = JSRaw $ '~' : translateVariableName arg

  | LStrConcat  <- op
  , (lhs:rhs:_) <- vars = translateBinaryOp "+" lhs rhs
  | LStrEq      <- op
  , (lhs:rhs:_) <- vars = translateBinaryOp "==" lhs rhs
  | LStrLt      <- op
  , (lhs:rhs:_) <- vars = translateBinaryOp "<" lhs rhs
  | LStrLen     <- op
  , (arg:_)     <- vars = JSProj (JSVar arg) "length"

  | (LStrInt ITNative)      <- op
  , (arg:_)                 <- vars = jsCall "parseInt" [JSVar arg]
  | (LIntStr ITNative)      <- op
  , (arg:_)                 <- vars = jsCall "String" [JSVar arg]
  | (LSExt ITNative ITBig)  <- op
  , (arg:_)                 <- vars = jsBigInt $ JSVar arg
  | (LTrunc ITBig ITNative) <- op
  , (arg:_)                 <- vars = jsMeth (JSVar arg) "valueOf" []
  | (LIntStr ITBig)         <- op
  , (arg:_)                 <- vars = jsMeth (JSVar arg) "toString" []
  | (LStrInt ITBig)         <- op
  , (arg:_)                 <- vars = jsBigInt $ JSVar arg
  | LFloatStr               <- op
  , (arg:_)                 <- vars = jsCall "String" [JSVar arg]
  | LStrFloat               <- op
  , (arg:_)                 <- vars = jsCall "parseFloat" [JSVar arg]
  | (LIntFloat ITNative)    <- op
  , (arg:_)                 <- vars = JSVar arg
  | (LFloatInt ITNative)    <- op
  , (arg:_)                 <- vars = JSVar arg
  | (LChInt ITNative)       <- op
  , (arg:_)                 <- vars = JSProj (JSVar arg) "charCodeAt(0)"
  | (LIntCh ITNative)       <- op
  , (arg:_)                 <- vars = jsCall "String.fromCharCode" [JSVar arg]

  | LFExp       <- op
  , (arg:_)     <- vars = jsCall "Math.exp" [JSVar arg]
  | LFLog       <- op
  , (arg:_)     <- vars = jsCall "Math.log" [JSVar arg]
  | LFSin       <- op
  , (arg:_)     <- vars = jsCall "Math.sin" [JSVar arg]
  | LFCos       <- op
  , (arg:_)     <- vars = jsCall "Math.cos" [JSVar arg]
  | LFTan       <- op
  , (arg:_)     <- vars = jsCall "Math.tan" [JSVar arg]
  | LFASin      <- op
  , (arg:_)     <- vars = jsCall "Math.asin" [JSVar arg]
  | LFACos      <- op
  , (arg:_)     <- vars = jsCall "Math.acos" [JSVar arg]
  | LFATan      <- op
  , (arg:_)     <- vars = jsCall "Math.atan" [JSVar arg]
  | LFSqrt      <- op
  , (arg:_)     <- vars = jsCall "Math.sqrt" [JSVar arg]
  | LFFloor     <- op
  , (arg:_)     <- vars = jsCall "Math.floor" [JSVar arg]
  | LFCeil      <- op
  , (arg:_)     <- vars = jsCall "Math.ceil" [JSVar arg]

  | LStrCons    <- op
  , (lhs:rhs:_) <- vars = translateBinaryOp "+" lhs rhs
  | LStrHead    <- op
  , (arg:_)     <- vars = JSIndex (JSVar arg) (JSRaw "0")
  | LStrRev     <- op
  , (arg:_)     <- vars = JSProj (JSVar arg) "split('').reverse().join('')"
  | LStrIndex   <- op
  , (lhs:rhs:_) <- vars = JSIndex (JSVar lhs) (JSVar rhs)
  | LStrTail    <- op
  , (arg:_)     <- vars = let v = translateVariableName arg in
                              JSRaw $ v ++ ".substr(1," ++ v ++ ".length-1)"
  where
    translateBinaryOp :: String -> LVar -> LVar -> JS
    translateBinaryOp f lhs rhs = JSOp f (JSVar lhs) (JSVar rhs)

    invokeMeth :: LVar -> String -> [LVar] -> JS
    invokeMeth obj meth args = jsMeth (JSVar obj) meth (map JSVar args)

translateExpression (SError msg) =
  JSError msg

translateExpression (SForeign _ _ "putStr" [(FString, var)]) =
  jsCall (idrRTNamespace ++ "print") [JSVar var]

translateExpression (SForeign _ _ fun args)
  | "[]=" `isSuffixOf` fun
  , (obj:idx:val:[]) <- args =
    JSRaw $ concat [object obj, index idx, assign val]

  | "[]" `isSuffixOf` fun
  , (obj:idx:[]) <- args =
    JSRaw $ object obj ++ index idx

  | "[" `isPrefixOf` fun && "]=" `isSuffixOf` fun
  , (obj:val:[]) <- args =
    JSRaw $ concat [object obj, '[' : name ++ "]", assign val]

  | "[" `isPrefixOf` fun && "]" `isSuffixOf` fun
  , (obj:[]) <- args =
    JSRaw $ object obj ++ '[' : name ++ "]"

  | "." `isPrefixOf` fun, "=" `isSuffixOf` fun
  , (obj:val:[]) <- args =
    JSRaw $ concat [object obj, field, assign val]

  | "." `isPrefixOf` fun
  , (obj:[]) <- args =
    JSRaw $ object obj ++ field

  | "." `isPrefixOf` fun
  , (obj:[(FUnit, _)]) <- args =
    JSRaw $ concat [object obj, method, "()"]

  | "." `isPrefixOf` fun
  , (obj:as) <- args =
    JSRaw $ concat [object obj, method, arguments as]

  | "[]=" `isSuffixOf` fun
  , (idx:val:[]) <- args =
    JSRaw $ concat [array, index idx, assign val]

  | "[]" `isSuffixOf` fun
  , (idx:[]) <- args =
    JSRaw $ array ++ index idx

  | otherwise = JSRaw $ fun ++ arguments args
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
      | FFunction   <- ffunc =
        idrRTNamespace ++ "ffiWrap(" ++ translateVariableName name ++ ")"
      | FFunctionIO <- ffunc =
        idrRTNamespace ++ "ffiWrap(" ++ translateVariableName name ++ ")"

    generateWrapper (_, name) =
      translateVariableName name

translateExpression patterncase
  | (SChkCase var cases) <- patterncase = caseHelper var cases "chk"
  | (SCase var cases)    <- patterncase = caseHelper var cases "cse"
  where
    caseHelper var cases param =
      JSApp (JSFunction [param] (
        JSCond $ map (expandCase param . translateCaseCond param) cases
      )) [JSVar var]

    expandCase :: String -> (Cond, JS) -> (JS, JS)
    expandCase _ (RawCond cond, branch) = (cond, branch)
    expandCase _ (CaseCond DefaultCase, branch) = (JSTrue , branch)
    expandCase var (CaseCond caseTy, branch)
      | ConCase tag <- caseTy =
          let checkCon = JSRaw var `jsInstanceOf` jsCon
              checkTag = (JSRaw $ show tag) `jsEq` jsTag (JSRaw var) in
              (checkCon `jsAnd` checkTag, branch)

      | TypeCase ty <- caseTy =
          let checkTy  = JSRaw var `jsInstanceOf` jsType
              checkTag = jsTypeTag (JSRaw var) `jsEq` JSType ty in
              (checkTy `jsAnd` checkTag, branch)

translateExpression (SCon i name vars) =
  JSNew (idrRTNamespace ++ "Con") [ JSRaw $ show i
                                  , JSArray $ map JSVar vars
                                  ]

translateExpression (SUpdate var e) =
  JSAssign (JSVar var) (translateExpression e)

translateExpression (SProj var i) =
  JSIndex (JSProj (JSVar var) "vars") (JSRaw $ show i)

translateExpression SNothing = JSNull

translateExpression e =
  JSError $ "Not yet implemented: " ++ filter (/= '\'') (show e)

data CaseType = ConCase Int
              | TypeCase JSType
              | DefaultCase
              deriving Eq

data Cond = CaseCond CaseType
          | RawCond JS

translateCaseCond :: String -> SAlt -> (Cond, JS)
translateCaseCond _ cse@(SDefaultCase _) =
  (CaseCond DefaultCase, translateCase Nothing cse)

translateCaseCond var cse@(SConstCase ty _)
  | StrType                  <- ty = matchHelper JSStringTy
  | PtrType                  <- ty = matchHelper JSPtrTy
  | Forgot                   <- ty = matchHelper JSForgotTy
  | (AType ATFloat)          <- ty = matchHelper JSFloatTy
  | (AType (ATInt ITBig))    <- ty = matchHelper JSIntegerTy
  | (AType (ATInt ITNative)) <- ty = matchHelper JSIntTy
  | (AType (ATInt ITChar))   <- ty = matchHelper JSCharTy
  where
    matchHelper :: JSType -> (Cond, JS)
    matchHelper ty = (CaseCond $ TypeCase ty, translateCase Nothing cse)

translateCaseCond var cse@(SConstCase cst@(BI _) _) =
  let cond = jsMeth (JSRaw var) "equals" [translateConstant cst] in
      (RawCond cond, translateCase Nothing cse)

translateCaseCond var cse@(SConstCase cst _) =
  let cond = JSRaw var `jsEq` translateConstant cst in
      (RawCond cond, translateCase Nothing cse)

translateCaseCond var cse@(SConCase _ tag _ _ _) =
  (CaseCond $ ConCase tag, translateCase (Just var) cse)

translateCase :: Maybe String -> SAlt -> JS
translateCase _          (SDefaultCase e) = translateExpression e
translateCase _          (SConstCase _ e) = translateExpression e
translateCase (Just var) (SConCase a _ _ vars e) =
  let params = map jsVar [a .. (a + length vars)] in
      jsMeth (JSFunction params (JSReturn $ translateExpression e)) "apply" [
        JSThis, JSProj (JSRaw var) "vars"
      ]
