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
           deriving Eq

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
        | JSFalse
        | JSArray [JS]
        | JSObject [(String, JS)]
        | JSString String
        | JSNum JSNum
        | JSAssign JS JS
        | JSAlloc String (Maybe JS)
        | JSIndex JS JS
        | JSCond [(JS, JS)]
        | JSTernary JS JS JS
        deriving Eq

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
  | JSAssign {} <- obj =
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

compileJS JSFalse =
  "false"

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

compileJS (JSTernary cond true false) =
  let c = compileJS cond
      t = compileJS true
      f = compileJS false in
      "(" ++ c ++ ")?(" ++ t ++ "):(" ++ f ++ ")"

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

jsLet :: String -> JS -> JS -> JS
jsLet name value body =
  JSApp (
    JSFunction [name] (
      JSReturn body
    )
  ) [value]

jsSubst :: String -> JS -> JS -> JS
jsSubst var new (JSVar old)
  | var == translateVariableName old = new

jsSubst var new (JSRaw old)
  | var == old = new

jsSubst var new (JSArray fields) =
  JSArray (map (jsSubst var new) fields)

jsSubst var new (JSNew con [tag, vals]) =
  JSNew con [tag, jsSubst var new vals]

jsSubst var new (JSNew con [JSFunction [] (JSReturn (JSApp fun vars))]) =
  JSNew con [JSFunction [] (
    JSReturn $ JSApp fun (map (jsSubst var new) vars)
  )]

jsSubst var new (JSApp (JSRaw "__IDRRT__tailcall") [JSFunction [] (
                  JSReturn (JSApp fun args)
                )]) =
                  JSApp (JSRaw "__IDRRT__tailcall") [JSFunction [] (
                    JSReturn $ JSApp fun (map (jsSubst var new) args)
                  )]

jsSubst var new (JSApp (JSFunction [arg] body) vals)
  | var /= arg =
      JSApp (JSFunction [arg] (
        jsSubst var new body
      )) $ map (jsSubst var new) vals

jsSubst var new (JSReturn ret) =
  JSReturn $ jsSubst var new ret

jsSubst _ _ js = js

inlineJS :: JS -> JS
inlineJS (JSApp (JSFunction [] (JSSeq ret)) []) =
  JSApp (JSFunction [] (JSSeq (map inlineJS ret))) []

inlineJS (JSApp (JSFunction [arg] (JSReturn ret)) [val])
  | JSNew con [tag, vals] <- ret
  , opt <- inlineJS val =
      JSNew con [tag, jsSubst arg opt vals]

  | JSNew con [JSFunction [] (JSReturn (JSApp fun vars))] <- ret
  , opt <- inlineJS val =
      JSNew con [JSFunction [] (
        JSReturn $ JSApp fun (map (jsSubst arg opt) vars)
      )]

  | JSApp (JSRaw "__IDRRT__tailcall") [JSFunction [] (
      JSReturn (JSApp fun args)
    )] <- ret
  , opt <- inlineJS val =
      JSApp (JSRaw "__IDRRT__tailcall") [JSFunction [] (
        JSReturn $ JSApp fun (map (jsSubst arg opt) args)
      )]

  | JSIndex (JSProj obj field) idx <- ret
  , opt <- inlineJS val =
      JSIndex (JSProj (
          jsSubst arg opt obj
        ) field
      ) (jsSubst arg opt idx)

  | JSOp op lhs rhs <- ret =
      JSOp op (jsSubst arg (inlineJS val) lhs) $
        (jsSubst arg (inlineJS val) rhs)

inlineJS (JSApp fun args) =
  JSApp (inlineJS fun) (map inlineJS args)

inlineJS (JSNew con args) =
  JSNew con $ map inlineJS args

inlineJS (JSArray fields) =
  JSArray (map inlineJS fields)

inlineJS (JSAssign lhs rhs) =
  JSAssign lhs (inlineJS rhs)

inlineJS (JSSeq seq) =
  JSSeq (map inlineJS seq)

inlineJS (JSFunction args body) =
  JSFunction args (inlineJS body)

inlineJS (JSProj (JSFunction args body) "apply") =
  JSProj (JSFunction args (inlineJS body)) "apply"

inlineJS (JSReturn js) =
  JSReturn $ inlineJS js

inlineJS (JSAlloc name (Just js)) =
  JSAlloc name (Just $ inlineJS js)

inlineJS (JSCond cases) =
  JSCond (map (second inlineJS) cases)

inlineJS (JSObject fields) =
  JSObject (map (second inlineJS) fields)

inlineJS js = js

reduceJS :: [JS] -> [JS]
reduceJS program =
  case partition findConstructors program of
    (candidates, rest) ->
      map reduce candidates ++ map (reduceCall (map funNames candidates)) rest
  where findConstructors :: JS -> Bool
        findConstructors js
          | (JSAlloc fun (Just (JSFunction [] (JSSeq body)))) <- js =
              reducable $ last body
          | otherwise = False
          where reducable :: JS -> Bool
                reducable (JSReturn js) = reducable js
                reducable (JSNew _ args) = and $ map reducable args
                reducable (JSArray fields) = and $ map reducable fields
                reducable (JSNum _) = True
                reducable JSNull = True
                reducable _ = False

        reduce :: JS -> JS
        reduce (JSAlloc fun (Just (JSFunction [] (JSSeq body))))
          | JSReturn js <- last body = (JSAlloc fun (Just js))
          | otherwise = error "this should not happen"

        funNames :: JS -> String
        funNames (JSAlloc fun _) = fun
        funNames _ = error "WTF?"

        reduceCall :: [String] -> JS -> JS
        reduceCall funs (JSApp (JSRaw "__IDRRT__tailcall") [JSFunction [] (
                          JSReturn (JSApp (JSRaw ret) [])
                        )])
          | ret `elem` funs = JSRaw ret

        reduceCall funs js@(JSApp (JSRaw fun) [])
          | fun `elem` funs = JSRaw fun
          | otherwise       = js

        reduceCall funs (JSAlloc fun (Just body)) =
          JSAlloc fun (Just $ reduceCall funs body)

        reduceCall funs (JSReturn js) =
          JSReturn $ reduceCall funs js

        reduceCall funs (JSSeq js) =
          JSSeq $ map (reduceCall funs) js

        reduceCall funs (JSNew con args) =
          JSNew con $ map (reduceCall funs) args

        reduceCall funs (JSFunction args body) =
          JSFunction args $ reduceCall funs body

        reduceCall funs (JSApp fun args) =
          JSApp (reduceCall funs fun) $ map (reduceCall funs) args

        reduceCall funs (JSProj obj field) =
          JSProj (reduceCall funs obj) field

        reduceCall funs (JSCond conds) =
          JSCond $ map (reduceCall funs *** reduceCall funs) conds

        reduceCall funs (JSAssign lhs rhs) =
          JSAssign (reduceCall funs lhs) (reduceCall funs rhs)

        reduceCall funs (JSArray fields) =
          JSArray $ map (reduceCall funs) fields

        reduceCall _ js = js

optimizeJS :: JS -> JS
optimizeJS = inlineLoop
  where inlineLoop :: JS -> JS
        inlineLoop js
          | opt <- inlineJS js
          , opt /= js = inlineLoop opt
          | otherwise = js

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
  path       <- getDataDir
  idrRuntime <- readFile $ path ++ "/js/Runtime-common.js"
  tgtRuntime <- readFile $ concat [path, "/js/Runtime", runtime, ".js"]
  writeFile filename $ header ++ (
    intercalate "\n" $ [ idrRuntime
                       , tgtRuntime
                       ] ++ functions ++ [mainLoop, invokeLoop]
    )

  setPermissions filename (emptyPermissions { readable   = True
                                            , executable = target == Node
                                            , writable   = True
                                            })
  where
    def :: [(String, SDecl)]
    def = map (first translateNamespace) definitions

    functions :: [String]
    functions =
      map compileJS (reduceJS $ map (optimizeJS . translateDeclaration) def)

    mainLoop :: String
    mainLoop = compileJS $
      JSAlloc "main" $ Just $ JSFunction [] (
        case target of
             Node       -> mainFun
             JavaScript -> jsMeth (JSRaw "window") "addEventListener" [
                 JSString "DOMContentLoaded", JSFunction [] (
                   mainFun
                 ), JSFalse
               ]
      )
      where
        mainFun :: JS
        mainFun = jsTailcall $ jsCall runMain []

        runMain :: String
        runMain = idrNamespace ++ translateName (MN 0 "runMain")

    invokeLoop :: String
    invokeLoop  = compileJS $ jsCall "main" []

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
translateNamespace (NS _ ns) = idrNamespace ++ concatMap translateIdentifier ns
translateNamespace (MN _ _)  = idrNamespace
translateNamespace (SN name) = idrNamespace ++ translateSpecialName name
translateNamespace NErased   = idrNamespace

translateName :: Name -> String
translateName (UN name)   = 'u' : translateIdentifier name
translateName (NS name _) = 'n' : translateName name
translateName (MN i name) = 'm' : translateIdentifier name ++ show i
translateName (SN name)   = 's' : translateSpecialName name
translateName NErased     = "e"

translateSpecialName :: SpecialName -> String
translateSpecialName name
  | WhereN i m n  <- name =
    'w' : translateName m ++ translateName n ++ show i
  | InstanceN n s <- name =
    'i' : translateName n ++ concatMap translateIdentifier s
  | ParentN n s   <- name =
    'p' : translateName n ++ translateIdentifier s
  | MethodN n     <- name =
    'm' : translateName n
  | CaseN n       <- name =
    'c' : translateName n

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
translateConstant (BI i)                   = jsBigInt $ JSString (show i)
translateConstant c =
  JSError $ "Unimplemented Constant: " ++ show c

translateDeclaration :: (String, SDecl) -> JS
translateDeclaration (path, SFun name params stackSize body)
  | (MN _ "APPLY")        <- name
  , (SLet var val next)   <- body
  , (SChkCase cvar cases) <- next =
    let lvar   = translateVariableName var
        lookup = "[" ++ lvar ++ ".tag](fn0,arg0," ++ lvar ++ ")" in
        JSSeq [ lookupTable [(var, "chk")] var cases
              , jsDecl $ JSFunction ["fn0", "arg0"] (
                  JSSeq [ JSAlloc "__var_0" (Just $ JSRaw "fn0")
                        , JSReturn $ jsLet (translateVariableName var) (
                            translateExpression val
                          ) (JSTernary (
                               (JSVar var `jsInstanceOf` jsCon) `jsAnd`
                               (hasProp lookupTableName (translateVariableName var))
                            ) (JSRaw $
                                 lookupTableName ++ lookup
                              ) JSNull
                            )
                        ]
                )
              ]

  | (MN _ "EVAL")        <- name
  , (SChkCase var cases) <- body =
    JSSeq [ lookupTable [] var cases
          , jsDecl $ JSFunction ["arg0"] (JSReturn $
              JSTernary (
                (JSRaw "arg0" `jsInstanceOf` jsCon) `jsAnd`
                (hasProp lookupTableName "arg0")
              ) (JSRaw $ lookupTableName ++ "[arg0.tag](arg0)") (JSRaw "arg0")
            )
          ]
  | otherwise =
    let fun = translateExpression body in
        jsDecl $ jsFun fun

  where
    hasProp :: String -> String -> JS
    hasProp table var =
      JSIndex (JSRaw table) (JSProj (JSRaw var) "tag")

    caseFun :: [(LVar, String)] -> LVar -> SAlt -> JS
    caseFun aux var cse =
      jsFunAux aux (translateCase (Just (translateVariableName var)) cse)

    getTag :: SAlt -> Maybe Int
    getTag (SConCase _ tag _ _ _) = Just tag
    getTag _                      = Nothing

    lookupTableName :: String
    lookupTableName = idrLTNamespace ++ translateName name

    lookupTable :: [(LVar, String)] -> LVar -> [SAlt] -> JS
    lookupTable aux var cases =
      JSAlloc lookupTableName $ Just (
        JSApp (JSFunction [] (
          JSSeq $ [
            JSAlloc "t" $ Just (JSArray [])
          ] ++ assignEntries (catMaybes $ map (lookupEntry aux var) cases) ++ [
            JSReturn (JSRaw "t")
          ]
        )) []
      )
      where
        assignEntries :: [(Int, JS)] -> [JS]
        assignEntries entries =
          map (\(tag, fun) ->
            JSAssign (JSIndex (JSRaw "t") (JSNum $ JSInt tag)) fun
          ) entries

        lookupEntry :: [(LVar, String)] ->  LVar -> SAlt -> Maybe (Int, JS)
        lookupEntry aux var alt = do
          tag <- getTag alt
          return (tag, caseFun aux var alt)

    jsDecl :: JS -> JS
    jsDecl = JSAlloc (path ++ translateName name) . Just

    jsFun body = jsFunAux [] body

    jsFunAux :: [(LVar, String)] -> JS -> JS
    jsFunAux aux body =
      JSFunction (p ++ map snd aux) (
        JSSeq $
        zipWith assignVar [0..] p ++
        map allocVar [numP .. (numP + stackSize - 1)] ++
        map assignAux aux ++
        [JSReturn body]
      )
      where
        numP :: Int
        numP = length params

        allocVar :: Int -> JS
        allocVar n = JSAlloc (jsVar n) Nothing

        assignVar :: Int -> String -> JS
        assignVar n s = JSAlloc (jsVar n)  (Just $ JSRaw s)

        assignAux :: (LVar, String) -> JS
        assignAux (var, val) =
          JSAssign (JSRaw $ translateVariableName var) (JSRaw val)

        p :: [String]
        p = map translateName params

translateVariableName :: LVar -> String
translateVariableName (Loc i) =
  jsVar i

translateExpression :: SExp -> JS
translateExpression (SLet name value body) =
  jsLet (translateVariableName name) (
    translateExpression value
  ) (translateExpression body)

translateExpression (SConst cst) =
  translateConstant cst

translateExpression (SV var) =
  JSVar var

translateExpression (SApp tc name vars)
  | False <- tc =
    jsTailcall $ translateFunctionCall name vars
  | True <- tc =
    JSNew (idrRTNamespace ++ "Cont") [JSFunction [] (
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

translateExpression (SForeign _ _ fun args) =
  ffi fun (map generateWrapper args)
  where
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
  JSNew (idrRTNamespace ++ "Con") [ JSNum $ JSInt i
                                  , JSArray $ map JSVar vars
                                  ]

translateExpression (SUpdate var e) =
  JSAssign (JSVar var) (translateExpression e)

translateExpression (SProj var i) =
  JSIndex (JSProj (JSVar var) "vars") (JSRaw $ show i)

translateExpression SNothing = JSNull

translateExpression e =
  JSError $ "Not yet implemented: " ++ filter (/= '\'') (show e)

data FFI = FFICode Char | FFIArg Int | FFIError String

ffi :: String -> [String] -> JS
ffi code args = let parsed = ffiParse code in
                    case ffiError parsed of
                         Just err -> JSError err
                         Nothing  -> JSRaw $ renderFFI parsed args
  where
    ffiParse :: String -> [FFI]
    ffiParse ""           = []
    ffiParse ['%']        = [FFIError "Invalid positional argument"]
    ffiParse ('%':'%':ss) = FFICode '%' : ffiParse ss
    ffiParse ('%':s:ss)
      | isDigit s =
         FFIArg (read $ s : takeWhile isDigit ss) : ffiParse (dropWhile isDigit ss)
      | otherwise =
          [FFIError "Invalid positional argument"]
    ffiParse (s:ss) = FFICode s : ffiParse ss

    ffiError :: [FFI] -> Maybe String
    ffiError []                 = Nothing
    ffiError ((FFIError s):xs)  = Just s
    ffiError (x:xs)             = ffiError xs

    renderFFI :: [FFI] -> [String] -> String
    renderFFI [] _ = ""
    renderFFI ((FFICode c) : fs) args = c : renderFFI fs args
    renderFFI ((FFIArg i) : fs) args
      | i < length args && i >= 0 = args !! i ++ renderFFI fs args
      | otherwise = "Argument index out of bounds"

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
