{-# LANGUAGE PatternGuards #-}

module IRTS.CodegenJavaScript (codegenJavaScript, JSTarget(..)) where

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

data JSInteger = JSBigZero
               | JSBigOne
               | JSBigInt Integer
               deriving Eq

data JSNum = JSInt Int
           | JSFloat Double
           | JSInteger JSInteger
           deriving Eq

data JS = JSRaw String
        | JSIdent String
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
        | JSChar String
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

compileJS (JSIdent ident) =
  ident

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

compileJS (JSChar chr) =
  chr

compileJS (JSNum num)
  | JSInt i                <- num = show i
  | JSFloat f              <- num = show f
  | JSInteger JSBigZero    <- num = "__IDRRT__ZERO"
  | JSInteger JSBigOne     <- num = "__IDRRT__ONE"
  | JSInteger (JSBigInt i) <- num = show i

compileJS (JSAssign lhs rhs) =
  compileJS lhs ++ "=" ++ compileJS rhs

compileJS (JSAlloc name val) =
  "var " ++ name ++ maybe "" ((" = " ++) . compileJS) val

compileJS (JSIndex lhs rhs) =
  compileJS lhs ++ "[" ++ compileJS rhs ++ "]"

compileJS (JSCond branches) =
  intercalate " else " $ map createIfBlock (eliminateDeadBranches branches)
  where
    eliminateDeadBranches (e@(JSTrue, _):_) = [e]
    eliminateDeadBranches (x:xs)            = x : eliminateDeadBranches xs
    eliminateDeadBranches []                = []

    createIfBlock (JSTrue, e) =
         "{\n"
      ++ "return " ++ compileJS e
      ++ ";\n}"
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
jsCall fun = JSApp (JSIdent fun)

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
jsType = JSIdent $ idrRTNamespace ++ "Type"

jsCon :: JS
jsCon = JSIdent $ idrRTNamespace ++ "Con"

jsTag :: JS -> JS
jsTag obj = JSProj obj "tag"

jsTypeTag :: JS -> JS
jsTypeTag obj = JSProj obj "type"

jsBigInt :: JS -> JS
jsBigInt (JSString "0") = JSNum $ JSInteger JSBigZero
jsBigInt (JSString "1") = JSNum $ JSInteger JSBigOne
jsBigInt val = JSApp (JSIdent $ idrRTNamespace ++ "bigInt") [val]

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
  | otherwise = JSVar old

jsSubst var new (JSIdent old)
  | var == old = new
  | otherwise = JSIdent old

jsSubst var new (JSArray fields) =
  JSArray (map (jsSubst var new) fields)

jsSubst var new (JSNew con [tag, vals]) =
  JSNew con [tag, jsSubst var new vals]

jsSubst var new (JSNew con [JSFunction [] (JSReturn (JSApp fun vars))]) =
  JSNew con [JSFunction [] (
    JSReturn $ JSApp (jsSubst var new fun) (map (jsSubst var new) vars)
  )]

jsSubst var new (JSApp (JSIdent "__IDRRT__tailcall") [JSFunction [] (
                  JSReturn (JSApp fun args)
                )]) =
                  JSApp (JSIdent "__IDRRT__tailcall") [JSFunction [] (
                    JSReturn $ JSApp (jsSubst var new fun) (map (jsSubst var new) args)
                  )]

jsSubst var new (JSApp (JSProj (JSFunction args body) "apply") vals)
  | var `notElem` args =
      JSApp (JSProj (JSFunction args (jsSubst var new body)) "apply") (
        map (jsSubst var new) vals
      )
  | otherwise =
      JSApp (JSProj (JSFunction args body) "apply") (
        map (jsSubst var new) vals
      )

jsSubst var new (JSApp (JSProj obj field) args) =
  JSApp (JSProj (jsSubst var new obj) field) $ map (jsSubst var new) args

jsSubst var new (JSApp (JSFunction [arg] body) vals)
  | var /= arg =
      JSApp (JSFunction [arg] (
        jsSubst var new body
      )) $ map (jsSubst var new) vals
  | otherwise =
      JSApp (JSFunction [arg] (
        body
      )) $ map (jsSubst var new) vals

jsSubst var new (JSReturn ret) =
  JSReturn $ jsSubst var new ret

jsSubst var new (JSProj obj field) =
  JSProj (jsSubst var new obj) field

jsSubst var new (JSSeq body) =
  JSSeq $ map (jsSubst var new) body

jsSubst var new (JSOp op lhs rhs) =
  JSOp op (jsSubst var new lhs) (jsSubst var new rhs)

jsSubst var new (JSIndex obj field) =
  JSIndex (jsSubst var new obj) (jsSubst var new field)

jsSubst var new (JSCond conds) =
  JSCond (map ((jsSubst var new) *** (jsSubst var new)) conds)

jsSubst _ _ js = js


isJSConstant :: JS -> Bool
isJSConstant js
  | JSString _ <- js = True
  | JSChar _   <- js = True
  | JSNum _    <- js = True
  | JSType _   <- js = True

  | JSApp (JSIdent "__IDRRT__bigInt") _ <- js = True
  | otherwise = False

inlineJS :: JS -> JS
inlineJS (JSApp (JSProj (JSFunction args (JSReturn body)) "apply") [
    JSThis,JSProj (JSIdent var) "vars"
  ])
  | var /= "cse" =
    inlineApply args body 0
  where
    inlineApply []     body _ = body
    inlineApply (a:as) body n =
      inlineApply as (
        jsSubst a (JSIndex (JSProj (JSIdent var) "vars") (JSNum (JSInt n))) body
      ) (n + 1)

inlineJS (JSApp (JSIdent "__IDR__mEVAL0") [val])
  | isJSConstant val = val

inlineJS (JSApp (JSIdent "__IDRRT__tailcall") [
    JSFunction [] (JSReturn val)
  ])
  | isJSConstant val = val

inlineJS (JSApp (JSFunction [] (JSSeq ret)) []) =
  JSApp (JSFunction [] (JSSeq (map inlineJS ret))) []

inlineJS (JSApp (JSFunction [arg] (JSReturn ret)) [val])
  | JSNew con [tag, vals] <- ret
  , opt <- inlineJS val =
      JSNew con [tag, jsSubst arg opt vals]

  | JSNew con [JSFunction [] (JSReturn (JSApp fun vars))] <- ret
  , opt <- inlineJS val =
      JSNew con [JSFunction [] (
        JSReturn $ JSApp (jsSubst arg opt fun) (map (jsSubst arg opt) vars)
      )]

  | JSApp (JSProj obj field) args <- ret
  , opt <- inlineJS val =
      JSApp (JSProj (jsSubst arg opt obj) field) $ map (jsSubst arg opt) args

  | JSIndex (JSProj obj field) idx <- ret
  , opt <- inlineJS val =
      JSIndex (JSProj (
          jsSubst arg opt obj
        ) field
      ) (jsSubst arg opt idx)

  | JSOp op lhs rhs <- ret
  , opt <- inlineJS val =
      JSOp op (jsSubst arg opt lhs) $
        (jsSubst arg opt rhs)

  | JSApp (JSIdent "__IDRRT__tailcall") [JSFunction [] (
      JSReturn (JSApp fun args)
    )] <- ret
  , opt <- inlineJS val =
      JSApp (JSIdent "__IDRRT__tailcall") [JSFunction [] (
        JSReturn $ JSApp (jsSubst arg opt fun) (map (jsSubst arg opt) args)
      )]

inlineJS (JSApp fun args) =
  JSApp (inlineJS fun) (map inlineJS args)

inlineJS (JSNew con args) =
  JSNew con $ map inlineJS args

inlineJS (JSArray fields) =
  JSArray (map inlineJS fields)

inlineJS (JSAssign lhs rhs) =
  JSAssign (inlineJS lhs) (inlineJS rhs)

inlineJS (JSSeq seq) =
  JSSeq (map inlineJS seq)

inlineJS (JSFunction args body) =
  JSFunction args (inlineJS body)

inlineJS (JSProj (JSFunction args body) field) =
  JSProj (JSFunction args (inlineJS body)) field

inlineJS (JSReturn js) =
  JSReturn $ inlineJS js

inlineJS (JSAlloc name (Just js)) =
  JSAlloc name (Just $ inlineJS js)

inlineJS (JSCond cases) =
  JSCond (map (second inlineJS) cases)

inlineJS (JSObject fields) =
  JSObject (map (second inlineJS) fields)

inlineJS (JSOp op lhs rhs) =
  JSOp op (inlineJS lhs) (inlineJS rhs)

inlineJS js = js

reduceJS :: [JS] -> [JS]
reduceJS js = reduceLoop [] ([], js)

funName :: JS -> String
funName (JSAlloc fun _) = fun

removeIDs :: [JS] -> [JS]
removeIDs js =
  case partition isID js of
       ([], rest)  -> rest
       (ids, rest) -> removeIDs $ map (removeIDCall (map idFor ids)) rest
  where isID :: JS -> Bool
        isID (JSAlloc _ (Just (JSFunction _ (JSSeq body))))
          | JSReturn (JSVar _) <- last body = True

        isID _ = False

        idFor :: JS -> (String, Int)
        idFor (JSAlloc fun (Just (JSFunction _ (JSSeq body))))
          | JSReturn (JSVar (Loc pos)) <- last body = (fun, pos)

        removeIDCall :: [(String, Int)] -> JS -> JS
        removeIDCall ids (JSApp (JSIdent "__IDRRT__tailcall") [JSFunction [] (
                           JSReturn (JSApp (JSIdent fun) args)
                         )])
          | Just pos <- lookup fun ids
          , pos < length args  = args !! pos

        removeIDCall ids (JSNew _ [JSFunction [] (
                           JSReturn (JSApp (JSIdent fun) args)
                         )])
          | Just pos <- lookup fun ids
          , pos < length args = args !! pos

        removeIDCall ids js@(JSApp id@(JSIdent fun) args)
          | Just pos <- lookup fun ids
          , pos < length args  = args !! pos

        removeIDCall ids (JSAlloc fun (Just body)) =
          JSAlloc fun (Just $ removeIDCall ids body)

        removeIDCall ids (JSReturn js) =
          JSReturn $ removeIDCall ids js

        removeIDCall ids (JSSeq js) =
          JSSeq $ map (removeIDCall ids) js

        removeIDCall ids (JSNew con args) =
          JSNew con $ map (removeIDCall ids) args

        removeIDCall ids (JSFunction args body) =
          JSFunction args $ removeIDCall ids body

        removeIDCall ids (JSApp fun args) =
          JSApp (removeIDCall ids fun) $ map (removeIDCall ids) args

        removeIDCall ids (JSProj obj field) =
          JSProj (removeIDCall ids obj) field

        removeIDCall ids (JSCond conds) =
          JSCond $ map (removeIDCall ids *** removeIDCall ids) conds

        removeIDCall ids (JSAssign lhs rhs) =
          JSAssign (removeIDCall ids lhs) (removeIDCall ids rhs)

        removeIDCall ids (JSArray fields) =
          JSArray $ map (removeIDCall ids) fields

        removeIDCall _ js = js

reduceConstant :: JS -> JS
reduceConstant (JSApp (JSIdent "__IDRRT__tailcall") [JSFunction [] (
                 JSReturn (JSApp (JSIdent "__IDR__mEVAL0") [JSNum num])
               )]) = JSNum num

reduceConstant (JSReturn ret) =
  JSReturn (reduceConstant ret)

reduceConstant (JSApp fun args) =
  JSApp (reduceConstant fun) (map reduceConstant args)

reduceConstant (JSArray fields) =
  JSArray (map reduceConstant fields)

reduceConstant (JSAlloc name (Just val)) =
  JSAlloc name $ Just (reduceConstant val)

reduceConstant (JSNew con args) =
  JSNew con (map reduceConstant args)

reduceConstant (JSProj obj field) =
  JSProj (reduceConstant obj) field

reduceConstant (JSCond conds) =
  JSCond $ map (reduceConstant *** reduceConstant) conds

reduceConstant (JSSeq seq) =
  JSSeq $ map reduceConstant seq

reduceConstant (JSFunction args body) =
  JSFunction args (reduceConstant body)

reduceConstant js = js

reduceConstants :: JS -> JS
reduceConstants js
  | ret <- reduceConstant js
  , ret /= js = reduceConstants ret
  | otherwise = js

reduceLoop :: [String] -> ([JS], [JS]) -> [JS]
reduceLoop reduced (cons, program) =
  case partition findConstructors program of
       ([], js)           -> cons ++ js
       (candidates, rest) ->
         let names = reduced ++ map funName candidates in
             reduceLoop names (
               cons ++ map reduce candidates, map (reduceCall names) rest
             )
  where findConstructors :: JS -> Bool
        findConstructors js
          | (JSAlloc fun (Just (JSFunction _ (JSSeq body)))) <- js =
              reducable $ last body
          | otherwise = False
          where reducable :: JS -> Bool
                reducable (JSReturn js) = reducable js
                reducable (JSNew _ args) = and $ map reducable args
                reducable (JSArray fields) = and $ map reducable fields
                reducable (JSNum _) = True
                reducable JSNull = True
                reducable (JSIdent _) = True
                reducable _ = False

        reduce :: JS -> JS
        reduce (JSAlloc fun (Just (JSFunction _ (JSSeq body))))
          | JSReturn js <- last body = (JSAlloc fun (Just js))

        reduce js = js

        reduceCall :: [String] -> JS -> JS
        reduceCall funs (JSApp (JSIdent "__IDRRT__tailcall") [JSFunction [] (
                          JSReturn (JSApp id@(JSIdent ret) _)
                        )])
          | ret `elem` funs = id

        reduceCall funs js@(JSApp id@(JSIdent fun) _)
          | fun `elem` funs = id

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

        reduceCall funs (JSIndex obj idx) =
          JSIndex (reduceCall funs obj) (reduceCall funs idx)

        reduceCall funs (JSOp op rhs lhs) =
          JSOp op (reduceCall funs rhs) (reduceCall funs lhs)

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
  path       <- (++) <$> getDataDir <*> (pure "/jsrts/")
  idrRuntime <- readFile $ path ++ "Runtime-common.js"
  tgtRuntime <- readFile $ concat [path, "Runtime", runtime, ".js"]
  jsbn       <- readFile $ path ++ "jsbn/jsbn.js"
  writeFile filename $ header ++ (
    intercalate "\n" $ [ jsbn
                       , idrRuntime
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
      map (compileJS . reduceConstants) ((reduceJS . removeIDs) $ map (optimizeJS . translateDeclaration) def)

    mainLoop :: String
    mainLoop = compileJS $
      JSAlloc "main" $ Just $ JSFunction [] (
        case target of
             Node       -> mainFun
             JavaScript -> jsMeth (JSIdent "window") "addEventListener" [
                 JSString "DOMContentLoaded", JSFunction [] (
                   mainFun
                 ), JSFalse
               ]
      )
      where
        mainFun :: JS
        mainFun = jsTailcall $ jsCall runMain []

        runMain :: String
        runMain = idrNamespace ++ translateName (sMN 0 "runMain")

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

translateConstant :: Const -> JS
translateConstant (I i)                    = JSNum (JSInt i)
translateConstant (Fl f)                   = JSNum (JSFloat f)
translateConstant (Ch '\DEL')              = JSChar "'\\u007F'"
translateConstant (Ch '\a')                = JSChar "'\\u0007'"
translateConstant (Ch '\SO')               = JSChar "'\\u000E'"
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
  | (MN _ ap)        <- name
  , (SLet var val next)   <- body
  , (SChkCase cvar cases) <- next
  , ap == txt "APPLY" =
    let lvar   = translateVariableName var
        lookup = "[" ++ lvar ++ ".tag](fn0,arg0," ++ lvar ++ ")" in
        JSSeq [ lookupTable [(var, "chk")] var cases
              , jsDecl $ JSFunction ["fn0", "arg0"] (
                  JSSeq [ JSAlloc "__var_0" (Just $ JSIdent "fn0")
                        , JSReturn $ jsLet (translateVariableName var) (
                            translateExpression val
                          ) (JSTernary (
                               (JSVar var `jsInstanceOf` jsCon) `jsAnd`
                               (hasProp lookupTableName (translateVariableName var))
                            ) (JSIdent $
                                 lookupTableName ++ lookup
                              ) JSNull
                            )
                        ]
                )
              ]

  | (MN _ ev)        <- name
  , (SChkCase var cases) <- body
  , ev == txt "EVAL" =
    JSSeq [ lookupTable [] var cases
          , jsDecl $ JSFunction ["arg0"] (JSReturn $
              JSTernary (
                (JSIdent "arg0" `jsInstanceOf` jsCon) `jsAnd`
                (hasProp lookupTableName "arg0")
              ) (JSRaw $ lookupTableName ++ "[arg0.tag](arg0)") (JSIdent "arg0")
            )
          ]
  | otherwise =
    let fun = translateExpression body in
        jsDecl $ jsFun fun

  where
    hasProp :: String -> String -> JS
    hasProp table var =
      JSIndex (JSIdent table) (JSProj (JSIdent var) "tag")

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
            JSReturn (JSIdent "t")
          ]
        )) []
      )
      where
        assignEntries :: [(Int, JS)] -> [JS]
        assignEntries entries =
          map (\(tag, fun) ->
            JSAssign (JSIndex (JSIdent "t") (JSNum $ JSInt tag)) fun
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
        map assignAux aux ++
        [JSReturn body]
      )
      where
        assignVar :: Int -> String -> JS
        assignVar n s = JSAlloc (jsVar n)  (Just $ JSIdent s)

        assignAux :: (LVar, String) -> JS
        assignAux (Loc var, val) =
          JSAlloc (jsVar var) (Just $ JSIdent val)

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

  | (LZExt _ ITBig)        <- op = jsBigInt $ jsCall "String" [JSVar (last vars)]
  | (LPlus (ATInt ITBig))  <- op
  , (lhs:rhs:_)            <- vars = invokeMeth lhs "add" [rhs]
  | (LMinus (ATInt ITBig)) <- op
  , (lhs:rhs:_)            <- vars = invokeMeth lhs "subtract" [rhs]
  | (LTimes (ATInt ITBig)) <- op
  , (lhs:rhs:_)            <- vars = invokeMeth lhs "multiply" [rhs]
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
  , (arg:_)                 <- vars = jsBigInt $ jsCall "String" [JSVar arg]
  | (LTrunc ITBig ITNative) <- op
  , (arg:_)                 <- vars = jsMeth (JSVar arg) "intValue" []
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
  , (arg:_)     <- vars = JSIndex (JSVar arg) (JSNum (JSInt 0))
  | LStrRev     <- op
  , (arg:_)     <- vars = JSProj (JSVar arg) "split('').reverse().join('')"
  | LStrIndex   <- op
  , (lhs:rhs:_) <- vars = JSIndex (JSVar lhs) (JSVar rhs)
  | LStrTail    <- op
  , (arg:_)     <- vars = let v = translateVariableName arg in
                              JSRaw $ v ++ ".substr(1," ++ v ++ ".length-1)"
  | LNullPtr    <- op
  , (_)         <- vars = JSNull

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
          let checkCon = JSIdent var `jsInstanceOf` jsCon
              checkTag = (JSNum $ JSInt tag) `jsEq` jsTag (JSIdent var) in
              (checkCon `jsAnd` checkTag, branch)

      | TypeCase ty <- caseTy =
          let checkTy  = JSIdent var `jsInstanceOf` jsType
              checkTag = jsTypeTag (JSIdent var) `jsEq` JSType ty in
              (checkTy `jsAnd` checkTag, branch)

translateExpression (SCon i name vars) =
  JSNew (idrRTNamespace ++ "Con") [ JSNum $ JSInt i
                                  , JSArray $ map JSVar vars
                                  ]

translateExpression (SUpdate var@(Loc i) e) =
  JSAssign (JSVar var) (translateExpression e)

translateExpression (SProj var i) =
  JSIndex (JSProj (JSVar var) "vars") (JSNum $ JSInt i)

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
  let cond = jsMeth (JSIdent var) "equals" [translateConstant cst] in
      (RawCond cond, translateCase Nothing cse)

translateCaseCond var cse@(SConstCase cst _) =
  let cond = JSIdent var `jsEq` translateConstant cst in
      (RawCond cond, translateCase Nothing cse)

translateCaseCond var cse@(SConCase _ tag _ _ _) =
  (CaseCond $ ConCase tag, translateCase (Just var) cse)

translateCase :: Maybe String -> SAlt -> JS
translateCase _          (SDefaultCase e) = translateExpression e
translateCase _          (SConstCase _ e) = translateExpression e
translateCase (Just var) (SConCase a _ _ vars e) =
  let params = map jsVar [a .. (a + length vars)] in
      jsMeth (JSFunction params (JSReturn $ translateExpression e)) "apply" [
        JSThis, JSProj (JSIdent var) "vars"
      ]
