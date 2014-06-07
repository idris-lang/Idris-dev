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
        | JSCond [(JS, JS)]
        | JSTernary JS JS JS
        | JSParens JS
        | JSWhile JS JS
        | JSFFI String [JS]
        | JSAnnotation JSAnnotation JS
        | JSNoop
        deriving Eq


data FFI = FFICode Char | FFIArg Int | FFIError String


ffi :: String -> [String] -> String
ffi code args = let parsed = ffiParse code in
                    case ffiError parsed of
                         Just err -> error err
                         Nothing  -> renderFFI parsed args
  where
    ffiParse :: String -> [FFI]
    ffiParse ""           = []
    ffiParse ['%']        = [FFIError $ "FFI - Invalid positional argument"]
    ffiParse ('%':'%':ss) = FFICode '%' : ffiParse ss
    ffiParse ('%':s:ss)
      | isDigit s =
         FFIArg (read $ s : takeWhile isDigit ss) : ffiParse (dropWhile isDigit ss)
      | otherwise =
          [FFIError $ "FFI - Invalid positional argument"]
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
      | otherwise = error "FFI - Argument index out of bounds"


compileJS :: JS -> String
compileJS JSNoop = ""

compileJS (JSAnnotation annotation js) =
  "/** @" ++ show annotation ++ " */\n" ++ compileJS js

compileJS (JSFFI raw args) =
  ffi raw (map compileJS args)

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

compileJS (JSString str) =
  "\"" ++ str ++ "\""

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
jsInstanceOf = JSBinOp "instanceof"


jsEq :: JS -> JS -> JS
jsEq = JSBinOp "=="

jsNotEq :: JS -> JS -> JS
jsNotEq = JSBinOp "!="

jsAnd :: JS -> JS -> JS
jsAnd = JSBinOp "&&"


jsOr :: JS -> JS -> JS
jsOr = JSBinOp "||"


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


jsError :: String -> JS
jsError err = JSApp (JSFunction [] (JSError err)) []

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


foldJS :: (JS -> a) -> (a -> a -> a) -> a -> JS -> a
foldJS tr add acc js =
  fold js
  where
    fold js
      | JSFunction args body <- js =
          add (tr js) (fold body)
      | JSSeq seq            <- js =
          add (tr js) $ foldl' add acc (map fold seq)
      | JSReturn ret         <- js =
          add (tr js) (fold ret)
      | JSApp lhs rhs        <- js =
          add (tr js) $ add (fold lhs) (foldl' add acc $ map fold rhs)
      | JSNew _ args         <- js =
          add (tr js) $ foldl' add acc $ map fold args
      | JSBinOp _ lhs rhs    <- js =
          add (tr js) $ add (fold lhs) (fold rhs)
      | JSPreOp _ val        <- js =
          add (tr js) $ fold val
      | JSPostOp _ val       <- js =
          add (tr js) $ fold val
      | JSProj obj _         <- js =
          add (tr js) (fold obj)
      | JSArray vals         <- js =
          add (tr js) $ foldl' add acc $ map fold vals
      | JSAssign lhs rhs     <- js =
          add (tr js) $ add (fold lhs) (fold rhs)
      | JSIndex lhs rhs      <- js =
          add (tr js) $ add (fold lhs) (fold rhs)
      | JSAlloc _ val        <- js =
          add (tr js) $ fromMaybe acc $ fmap fold val
      | JSTernary c t f      <- js =
          add (tr js) $ add (fold c) (add (fold t) (fold f))
      | JSParens val         <- js =
          add (tr js) $ fold val
      | JSCond conds         <- js =
          add (tr js) $ foldl' add acc $ map (uncurry add . (fold *** fold)) conds
      | JSWhile cond body    <- js =
          add (tr js) $ add (fold cond) (fold body)
      | JSFFI raw args       <- js =
          add (tr js) $ foldl' add acc $ map fold args
      | JSAnnotation a js    <- js =
          add (tr js) $ fold js
      | otherwise                  =
          tr js


transformJS :: (JS -> JS) -> JS -> JS
transformJS tr js =
  transformHelper js
  where
    transformHelper :: JS -> JS
    transformHelper js
      | JSFunction args body <- js = JSFunction args $ tr body
      | JSSeq seq            <- js = JSSeq $ map tr seq
      | JSReturn ret         <- js = JSReturn $ tr ret
      | JSApp lhs rhs        <- js = JSApp (tr lhs) $ map tr rhs
      | JSNew con args       <- js = JSNew con $ map tr args
      | JSBinOp op lhs rhs   <- js = JSBinOp op (tr lhs) (tr rhs)
      | JSPreOp op val       <- js = JSPreOp op (tr val)
      | JSPostOp op val      <- js = JSPostOp op (tr val)
      | JSProj obj field     <- js = JSProj (tr obj) field
      | JSArray vals         <- js = JSArray $ map tr vals
      | JSAssign lhs rhs     <- js = JSAssign (tr lhs) (tr rhs)
      | JSAlloc var val      <- js = JSAlloc var $ fmap tr val
      | JSIndex lhs rhs      <- js = JSIndex (tr lhs) (tr rhs)
      | JSCond conds         <- js = JSCond $ map (tr *** tr) conds
      | JSTernary c t f      <- js = JSTernary (tr c) (tr t) (tr f)
      | JSParens val         <- js = JSParens $ tr val
      | JSWhile cond body    <- js = JSWhile (tr cond) (tr body)
      | JSFFI raw args       <- js = JSFFI raw (map tr args)
      | JSAnnotation a js    <- js = JSAnnotation a (tr js)
      | otherwise                  = js


moveJSDeclToTop :: String -> [JS] -> [JS]
moveJSDeclToTop decl js = move ([], js)
  where
    move :: ([JS], [JS]) -> [JS]
    move (front, js@(JSAnnotation _ (JSAlloc name _)):back)
      | name == decl = js : front ++ back

    move (front, js@(JSAlloc name _):back)
      | name == decl = js : front ++ back

    move (front, js:back) =
      move (front ++ [js], back)


jsSubst :: JS -> JS -> JS -> JS
jsSubst var new old
  | var == old = new

jsSubst (JSIdent var) new (JSVar old)
  | var == translateVariableName old = new
  | otherwise                        = JSVar old

jsSubst var new old@(JSIdent _)
  | var == old = new
  | otherwise  = old

jsSubst var new (JSArray fields) =
  JSArray (map (jsSubst var new) fields)

jsSubst var new (JSNew con vals) =
  JSNew con $ map (jsSubst var new) vals

jsSubst (JSIdent var) new (JSApp (JSProj (JSFunction args body) "apply") vals)
  | var `notElem` args =
      JSApp (JSProj (JSFunction args (jsSubst (JSIdent var) new body)) "apply") (
        map (jsSubst (JSIdent var) new) vals
      )
  | otherwise =
      JSApp (JSProj (JSFunction args body) "apply") (
        map (jsSubst (JSIdent var) new) vals
      )

jsSubst (JSIdent var) new (JSApp (JSFunction [arg] body) vals)
  | var /= arg =
      JSApp (JSFunction [arg] (
        jsSubst (JSIdent var) new body
      )) $ map (jsSubst (JSIdent var) new) vals
  | otherwise =
      JSApp (JSFunction [arg] (
        body
      )) $ map (jsSubst (JSIdent var) new) vals

jsSubst var new js = transformJS (jsSubst var new) js


removeAllocations :: JS -> JS
removeAllocations (JSSeq body) =
  let opt = removeHelper (map removeAllocations body) in
      case opt of
           [ret] -> ret
           _     -> JSSeq opt
  where
    removeHelper :: [JS] -> [JS]
    removeHelper [js] = [js]
    removeHelper ((JSAlloc name (Just val@(JSIdent _))):js) =
      map (jsSubst (JSIdent name) val) (removeHelper js)
    removeHelper (j:js) = j : removeHelper js

removeAllocations js = transformJS removeAllocations js


isJSConstant :: JS -> Bool
isJSConstant js
  | JSString _   <- js = True
  | JSNum _      <- js = True
  | JSType _     <- js = True
  | JSNull       <- js = True
  | JSArray vals <- js = all isJSConstant vals

  | JSApp (JSIdent "__IDRRT__bigInt") _ <- js = True

  | otherwise = False

isJSConstantConstructor :: [String] -> JS -> Bool
isJSConstantConstructor constants js
  | isJSConstant js =
      True
  | JSArray vals <- js =
      all (isJSConstantConstructor constants) vals
  | JSNew "__IDRRT__Con" args <- js =
      all (isJSConstantConstructor constants) args
  | JSIndex (JSProj (JSIdent name) "vars") (JSNum _) <- js
  , name `elem` constants =
      True
  | JSIdent name <- js
  , name `elem` constants =
      True
  | otherwise = False


inlineJS :: JS -> JS
inlineJS = inlineAssign . inlineError . inlineApply . inlineCaseMatch . inlineJSLet
  where
    inlineJSLet :: JS -> JS
    inlineJSLet (JSApp (JSFunction [arg] (JSReturn ret)) [val])
      | opt <- inlineJSLet val =
          inlineJS $ jsSubst (JSIdent arg) opt ret

    inlineJSLet js = transformJS inlineJSLet js


    inlineCaseMatch (JSReturn (JSApp (JSFunction ["cse"] body) [val]))
      | opt <- inlineCaseMatch val =
          inlineCaseMatch $ jsSubst (JSIdent "cse") opt body

    inlineCaseMatch js = transformJS inlineCaseMatch js


    inlineApply js
      | JSApp (
          JSProj (JSFunction args (JSReturn body)) "apply"
        ) [JSThis, JSProj var "vars"] <- js =
          inlineApply $ inlineApply' var args body 0
      | JSReturn (JSApp  (
          JSProj (JSFunction args body@(JSCond _)) "apply"
        ) [JSThis, JSProj var "vars"]) <- js =
          inlineApply $ inlineApply' var args body 0
      where
        inlineApply' _   []     body _ = body
        inlineApply' var (a:as) body n =
          inlineApply' var as (
            jsSubst (JSIdent a) (
              JSIndex (JSProj var "vars") (JSNum (JSInt n))
            ) body
          ) (n + 1)

    inlineApply js = transformJS inlineApply js


    inlineError (JSReturn (JSApp (JSFunction [] error@(JSError _)) [])) =
      inlineError error

    inlineError js = transformJS inlineError js


    inlineAssign (JSAssign lhs rhs)
      | JSVar _ <- lhs
      , JSVar _ <- rhs
      , lhs == rhs =
          lhs

    inlineAssign (JSAssign lhs rhs)
      | JSIdent _ <- lhs
      , JSIdent _ <- rhs
      , lhs == rhs =
          lhs

    inlineAssign js = transformJS inlineAssign js


removeEval :: [JS] -> [JS]
removeEval js =
  let (ret, isReduced) = checkEval js in
      if isReduced
          then removeEvalApp ret
          else ret
  where
    removeEvalApp js = catMaybes (map removeEvalApp' js)
      where
        removeEvalApp' :: JS -> Maybe JS
        removeEvalApp' (JSAlloc "__IDR__mEVAL0" _) = Nothing
        removeEvalApp' js = Just $ transformJS match js
          where
            match (JSApp (JSIdent "__IDR__mEVAL0") [val]) = val
            match js = transformJS match js

    checkEval :: [JS] -> ([JS], Bool)
    checkEval js = foldr f ([], False) $ map checkEval' js
      where
        f :: (Maybe JS, Bool) -> ([JS], Bool) -> ([JS], Bool)
        f (Just js, isReduced) (ret, b) = (js : ret, isReduced || b)
        f (Nothing, isReduced) (ret, b) = (ret, isReduced || b)


        checkEval' :: JS -> (Maybe JS, Bool)
        checkEval' (JSAlloc "__IDRLT__EVAL" (Just (JSApp (JSFunction [] (
            JSSeq [ _
                  , JSReturn (JSIdent "t")
                  ]
          )) []))) = (Nothing, True)

        checkEval' js = (Just js, False)


reduceJS :: [JS] -> [JS]
reduceJS js = moveJSDeclToTop "__IDRRT__Con" $ reduceLoop [] ([], js)


funName :: JS -> String
funName (JSAlloc fun _) = fun


elimDeadLoop :: [JS] -> [JS]
elimDeadLoop js
  | ret <- deadEvalApplyCases js
  , ret /= js = elimDeadLoop ret
  | otherwise = js


deadEvalApplyCases :: [JS] -> [JS]
deadEvalApplyCases js =
  let tags = sort $ nub $ concatMap (getTags) js in
      map (removeHelper tags) js
      where
        getTags :: JS -> [Int]
        getTags = foldJS match (++) []
          where
            match js
              | JSNew "__IDRRT__Con" [JSNum (JSInt tag), _] <- js = [tag]
              | otherwise                                         = []


        removeHelper :: [Int] -> JS -> JS
        removeHelper tags (JSAlloc fun (Just (
            JSApp (JSFunction [] (JSSeq seq)) []))
          ) =
            (JSAlloc fun (Just (
              JSApp (JSFunction [] (JSSeq $ remover tags seq)) []))
            )

        removeHelper _ js = js


        remover :: [Int] -> [JS] -> [JS]
        remover tags (
            j@(JSAssign ((JSIndex (JSIdent "t") (JSNum (JSInt tag)))) _):js
          )
          | tag `notElem` tags = remover tags js

        remover tags (j:js) = j : remover tags js
        remover _    []     = []


initConstructors :: [JS] -> [JS]
initConstructors js =
    let tags = nub $ sort $ concat (map getTags js) in
        rearrangePrelude $ map createConstant tags ++ replaceConstructors tags js
      where
        rearrangePrelude :: [JS] -> [JS]
        rearrangePrelude = moveJSDeclToTop $ idrRTNamespace ++ "Con"


        getTags :: JS -> [Int]
        getTags = foldJS match (++) []
          where
            match js
              | JSNew "__IDRRT__Con" [JSNum (JSInt tag), JSArray []] <- js = [tag]
              | otherwise                                                  = []


        replaceConstructors :: [Int] -> [JS] -> [JS]
        replaceConstructors tags js = map (replaceHelper tags) js
          where
            replaceHelper :: [Int] -> JS -> JS
            replaceHelper tags (JSNew "__IDRRT__Con" [JSNum (JSInt tag), JSArray []])
              | tag `elem` tags = JSIdent (idrCTRNamespace ++ show tag)

            replaceHelper tags js = transformJS (replaceHelper tags) js


        createConstant :: Int -> JS
        createConstant tag =
          JSAlloc (idrCTRNamespace ++ show tag) (Just (
            JSNew (idrRTNamespace ++ "Con") [JSNum (JSInt tag), JSArray []]
          ))


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
          , pos < length args  = removeIDCall ids (args !! pos)

        removeIDCall ids (JSNew _ [JSFunction [] (
                           JSReturn (JSApp (JSIdent fun) args)
                         )])
          | Just pos <- lookup fun ids
          , pos < length args = removeIDCall ids (args !! pos)

        removeIDCall ids js@(JSApp id@(JSIdent fun) args)
          | Just pos <- lookup fun ids
          , pos < length args  = removeIDCall ids (args !! pos)

        removeIDCall ids js = transformJS (removeIDCall ids) js


inlineFunction :: String -> [String] -> JS -> JS -> JS
inlineFunction fun args body js = inline' js
  where
    inline' :: JS -> JS
    inline' (JSApp (JSIdent name) vals)
      | name == fun =
          let (js, phs) = insertPlaceHolders args body in
              inline' $ foldr (uncurry jsSubst) js (zip phs vals)

    inline' js = transformJS inline' js

    insertPlaceHolders :: [String] -> JS -> (JS, [JS])
    insertPlaceHolders args body = insertPlaceHolders' args body []
      where
        insertPlaceHolders' :: [String] -> JS -> [JS] -> (JS, [JS])
        insertPlaceHolders' (a:as) body ph
          | (body', ph') <- insertPlaceHolders' as body ph =
              let phvar = JSIdent $ "__PH_" ++ show (length ph') in
                  (jsSubst (JSIdent a) phvar body', phvar : ph')

        insertPlaceHolders' [] body ph = (body, ph)


inlineFunctions :: [JS] -> [JS]
inlineFunctions js =
  inlineHelper ([], js)
  where
    inlineHelper :: ([JS], [JS]) -> [JS]
    inlineHelper (front , (JSAlloc fun (Just (JSFunction args body))):back)
      | countAll fun front + countAll fun back == 0 =
         inlineHelper (front, back)
      | Just new <- inlineAble (
            countAll fun front + countAll fun back
          ) fun args body =
              let f = map (inlineFunction fun args new) in
                  inlineHelper (f front, f back)

    inlineHelper (front, next:back) = inlineHelper (front ++ [next], back)
    inlineHelper (front, [])        = front


    inlineAble :: Int -> String -> [String] -> JS -> Maybe JS
    inlineAble 1 fun args (JSReturn body)
      | nonRecur fun body =
          if all (<= 1) (map ($ body) (map countIDOccurences args))
             then Just body
             else Nothing

    inlineAble _ _ _ _ = Nothing


    nonRecur :: String -> JS -> Bool
    nonRecur name body = countInvokations name body == 0


    countAll :: String -> [JS] -> Int
    countAll name js = sum $ map (countInvokations name) js


    countIDOccurences :: String -> JS -> Int
    countIDOccurences name = foldJS match (+) 0
      where
        match :: JS -> Int
        match js
          | JSIdent ident <- js
          , name == ident = 1
          | otherwise     = 0


    countInvokations :: String -> JS -> Int
    countInvokations name = foldJS match (+) 0
      where
        match :: JS -> Int
        match js
          | JSApp (JSIdent ident) _ <- js
          , name == ident = 1
          | JSNew con _             <- js
          , name == con   = 1
          | otherwise     = 0


reduceContinuations :: JS -> JS
reduceContinuations = inlineTC . reduceJS
  where
    reduceJS :: JS -> JS
    reduceJS (JSNew "__IDRRT__Cont" [JSFunction [] (
        JSReturn js@(JSNew "__IDRRT__Cont" [JSFunction [] body])
      )]) = reduceJS js

    reduceJS js = transformJS reduceJS js


    inlineTC :: JS -> JS
    inlineTC js
      | JSApp (JSIdent "__IDRRT__tailcall") [JSFunction [] (
            JSReturn (JSNew "__IDRRT__Cont" [JSFunction [] (
              JSReturn ret@(JSApp (JSIdent "__IDRRT__tailcall") [JSFunction [] (
                  JSReturn (JSNew "__IDRRT__Cont" _)
              )])
            )])
          )] <- js = inlineTC ret

    inlineTC js = transformJS inlineTC js




reduceConstant :: JS -> JS
reduceConstant
  (JSApp (JSIdent "__IDRRT__tailcall") [JSFunction [] (
    JSReturn (JSApp (JSIdent "__IDR__mEVAL0") [val])
  )])
  | JSNum num          <- val = val
  | JSBinOp op lhs rhs <- val =
      JSParens $ JSBinOp op (reduceConstant lhs) (reduceConstant rhs)

  | JSApp (JSProj lhs op) [rhs] <- val
  , op `elem` [ "subtract"
              , "add"
              , "multiply"
              , "divide"
              , "mod"
              , "equals"
              , "lesser"
              , "lesserOrEquals"
              , "greater"
              , "greaterOrEquals"
              ] = val

reduceConstant (JSApp ident [(JSParens js)]) =
  JSApp ident [reduceConstant js]

reduceConstant js = transformJS reduceConstant js


reduceConstants :: JS -> JS
reduceConstants js
  | ret <- reduceConstant js
  , ret /= js = reduceConstants ret
  | otherwise = js


elimDuplicateEvals :: JS -> JS
elimDuplicateEvals (JSAlloc fun (Just (JSFunction args (JSSeq seq)))) =
  JSAlloc fun $ Just (JSFunction args $ JSSeq (elimHelper seq))
  where
    elimHelper :: [JS] -> [JS]
    elimHelper (j@(JSAlloc var (Just val)):js) =
      j : map (jsSubst val (JSIdent var)) (elimHelper js)
    elimHelper (j:js) =
      j : elimHelper js
    elimHelper [] = []

elimDuplicateEvals js = js


optimizeRuntimeCalls :: String -> String -> [JS] -> [JS]
optimizeRuntimeCalls fun tc js =
  optTC tc : map optHelper js
  where
    optHelper :: JS -> JS
    optHelper (JSApp (JSIdent "__IDRRT__tailcall") [
        JSFunction [] (JSReturn (JSApp (JSIdent n) args))
      ])
      | n == fun = JSApp (JSIdent tc) $ map optHelper args

    optHelper js = transformJS optHelper js


    optTC :: String -> JS
    optTC tc@"__IDRRT__EVALTC" =
      JSAlloc tc (Just $ JSFunction ["arg0"] (
        JSSeq [ JSAlloc "ret" $ Just (
                  JSTernary (
                    (JSIdent "arg0" `jsInstanceOf` jsCon) `jsAnd`
                    (hasProp "__IDRLT__EVAL" "arg0")
                  ) (JSApp
                      (JSIndex
                        (JSIdent "__IDRLT__EVAL")
                        (JSProj (JSIdent "arg0") "tag")
                      )
                      [JSIdent "arg0"]
                  ) (JSIdent "arg0")
                )
              , JSWhile (JSIdent "ret" `jsInstanceOf` (JSIdent "__IDRRT__Cont")) (
                  JSAssign (JSIdent "ret") (
                    JSApp (JSProj (JSIdent "ret") "k") []
                  )
                )
              , JSReturn $ JSIdent "ret"
              ]
      ))

    optTC tc@"__IDRRT__APPLYTC" =
      JSAlloc tc (Just $ JSFunction ["fn0", "arg0"] (
        JSSeq [ JSAlloc "ret" $ Just (
                  JSTernary (
                    (JSIdent "fn0" `jsInstanceOf` jsCon) `jsAnd`
                    (hasProp "__IDRLT__APPLY" "fn0")
                  ) (JSApp
                      (JSIndex
                        (JSIdent "__IDRLT__APPLY")
                        (JSProj (JSIdent "fn0") "tag")
                      )
                      [JSIdent "fn0", JSIdent "arg0", JSIdent "fn0"]
                  ) JSNull
                )
              , JSWhile (JSIdent "ret" `jsInstanceOf` (JSIdent "__IDRRT__Cont")) (
                  JSAssign (JSIdent "ret") (
                    JSApp (JSProj (JSIdent "ret") "k") []
                  )
                )
              , JSReturn $ JSIdent "ret"
              ]
      ))


    hasProp :: String -> String -> JS
    hasProp table var =
      JSIndex (JSIdent table) (JSProj (JSIdent var) "tag")


unfoldLookupTable :: [JS] -> [JS]
unfoldLookupTable input =
  let (evals, evalunfold)   = unfoldLT "__IDRLT__EVAL" input
      (applys, applyunfold) = unfoldLT "__IDRLT__APPLY" evalunfold
      js                    = applyunfold in
      adaptRuntime $ expandCons evals applys js
  where
    adaptRuntime :: [JS] -> [JS]
    adaptRuntime =
      adaptEvalTC . adaptApplyTC . adaptEval . adaptApply . adaptCon


    adaptApply :: [JS] -> [JS]
    adaptApply js = adaptApply' [] js
      where
        adaptApply' :: [JS] -> [JS] -> [JS]
        adaptApply' front ((JSAlloc "__IDR__mAPPLY0" (Just _)):back) =
          front ++ (new:back)

        adaptApply' front (next:back) =
          adaptApply' (front ++ [next]) back

        adaptApply' front [] = front

        new =
          JSAlloc "__IDR__mAPPLY0" (Just $ JSFunction ["mfn0", "marg0"] (JSReturn $
              JSTernary (
                (JSIdent "mfn0" `jsInstanceOf` jsCon) `jsAnd`
                (JSProj (JSIdent "mfn0") "app")
              ) (JSApp
                  (JSProj (JSIdent "mfn0") "app")
                  [JSIdent "mfn0", JSIdent "marg0"]
              ) JSNull
            )
          )


    adaptApplyTC :: [JS] -> [JS]
    adaptApplyTC js = adaptApplyTC' [] js
      where
        adaptApplyTC' :: [JS] -> [JS] -> [JS]
        adaptApplyTC' front ((JSAlloc "__IDRRT__APPLYTC" (Just _)):back) =
          front ++ (new:back)

        adaptApplyTC' front (next:back) =
          adaptApplyTC' (front ++ [next]) back

        adaptApplyTC' front [] = front

        new =
          JSAlloc "__IDRRT__APPLYTC" (Just $ JSFunction ["mfn0", "marg0"] (
            JSSeq [ JSAlloc "ret" $ Just (
                      JSTernary (
                        (JSIdent "mfn0" `jsInstanceOf` jsCon) `jsAnd`
                        (JSProj (JSIdent "mfn0") "app")
                      ) (JSApp
                          (JSProj (JSIdent "mfn0") "app")
                          [JSIdent "mfn0", JSIdent "marg0"]
                      ) JSNull
                    )
                  , JSWhile (JSIdent "ret" `jsInstanceOf` (JSIdent "__IDRRT__Cont")) (
                      JSAssign (JSIdent "ret") (
                        JSApp (JSProj (JSIdent "ret") "k") []
                      )
                    )
                  , JSReturn $ JSIdent "ret"
                  ]
          ))


    adaptEval :: [JS] -> [JS]
    adaptEval js = adaptEval' [] js
      where
        adaptEval' :: [JS] -> [JS] -> [JS]
        adaptEval' front ((JSAlloc "__IDR__mEVAL0" (Just _)):back) =
          front ++ (new:back)

        adaptEval' front (next:back) =
          adaptEval' (front ++ [next]) back

        adaptEval' front [] = front

        new =
          JSAlloc "__IDR__mEVAL0" (Just $ JSFunction ["marg0"] (JSReturn $
              JSTernary (
                (JSIdent "marg0" `jsInstanceOf` jsCon) `jsAnd`
                (JSProj (JSIdent "marg0") "eval")
              ) (JSApp
                  (JSProj (JSIdent "marg0") "eval")
                  [JSIdent "marg0"]
              ) (JSIdent "marg0")
            )
          )


    adaptEvalTC :: [JS] -> [JS]
    adaptEvalTC js = adaptEvalTC' [] js
      where
        adaptEvalTC' :: [JS] -> [JS] -> [JS]
        adaptEvalTC' front ((JSAlloc "__IDRRT__EVALTC" (Just _)):back) =
          front ++ (new:back)

        adaptEvalTC' front (next:back) =
          adaptEvalTC' (front ++ [next]) back

        adaptEvalTC' front [] = front

        new =
          JSAlloc "__IDRRT__EVALTC" (Just $ JSFunction ["marg0"] (
            JSSeq [ JSAlloc "ret" $ Just (
                      JSTernary (
                        (JSIdent "marg0" `jsInstanceOf` jsCon) `jsAnd`
                        (JSProj (JSIdent "marg0") "eval")
                      ) (JSApp
                          (JSProj (JSIdent "marg0") "eval")
                          [JSIdent "marg0"]
                      ) (JSIdent "marg0")
                    )
                  , JSWhile (JSIdent "ret" `jsInstanceOf` (JSIdent "__IDRRT__Cont")) (
                      JSAssign (JSIdent "ret") (
                        JSApp (JSProj (JSIdent "ret") "k") []
                      )
                    )
                  , JSReturn $ JSIdent "ret"
                  ]
          ))


    adaptCon js =
      adaptCon' [] js
      where
        adaptCon' front ((JSAnnotation _ (JSAlloc "__IDRRT__Con" _)):back) =
          front ++ (new:back)

        adaptCon' front (next:back) =
          adaptCon' (front ++ [next]) back

        adaptCon' front [] = front


        new =
          JSAnnotation JSConstructor $
            JSAlloc "__IDRRT__Con" (Just $
              JSFunction newArgs (
                JSSeq (map newVar newArgs)
              )
            )
          where
            newVar var = JSAssign (JSProj JSThis var) (JSIdent var)
            newArgs = ["tag", "eval", "app", "vars"]


    unfoldLT :: String -> [JS] -> ([Int], [JS])
    unfoldLT lt js =
      let (table, code) = extractLT lt js
          expanded      = expandLT lt table in
          (map fst expanded, map snd expanded ++ code)


    expandCons :: [Int] -> [Int] -> [JS] -> [JS]
    expandCons evals applys js =
      map expandCons' js
      where
        expandCons' :: JS -> JS
        expandCons' (JSNew "__IDRRT__Con" [JSNum (JSInt tag), JSArray args])
          | evalid  <- getId "__IDRLT__EVAL"  tag evals
          , applyid <- getId "__IDRLT__APPLY" tag applys =
              JSNew "__IDRRT__Con" [ JSNum (JSInt tag)
                                   , maybe JSNull JSIdent evalid
                                   , maybe JSNull JSIdent applyid
                                   , JSArray (map expandCons' args)
                                   ]

        expandCons' js = transformJS expandCons' js


        getId :: String -> Int -> [Int] -> Maybe String
        getId lt tag entries
          | tag `elem` entries = Just $ ltIdentifier lt tag
          | otherwise          = Nothing


    ltIdentifier :: String -> Int -> String
    ltIdentifier "__IDRLT__EVAL"  id = idrLTNamespace ++ "EVAL" ++ show id
    ltIdentifier "__IDRLT__APPLY" id = idrLTNamespace ++ "APPLY" ++ show id


    extractLT :: String -> [JS] -> (JS, [JS])
    extractLT lt js =
      extractLT' ([], js)
        where
          extractLT' :: ([JS], [JS]) -> (JS, [JS])
          extractLT' (front, js@(JSAlloc fun _):back)
            | fun == lt = (js, front ++ back)

          extractLT' (front, js:back) = extractLT' (front ++ [js], back)
          extractLT' (front, back)    = (JSNoop, front ++ back)


    expandLT :: String -> JS -> [(Int, JS)]
    expandLT lt (
        JSAlloc _ (Just (JSApp (JSFunction [] (JSSeq seq)) []))
      ) = catMaybes (map expandEntry seq)
          where
            expandEntry :: JS -> Maybe (Int, JS)
            expandEntry (JSAssign (JSIndex _ (JSNum (JSInt id))) body) =
              Just $ (id, JSAlloc (ltIdentifier lt id) (Just body))

            expandEntry js = Nothing

    expandLT lt JSNoop = []


removeInstanceChecks :: JS -> JS
removeInstanceChecks (JSCond conds) =
  removeNoopConds $ JSCond $ eliminateDeadBranches $ map (
    removeHelper *** removeInstanceChecks
  ) conds
  where
    removeHelper (
        JSBinOp "&&" (JSBinOp "instanceof" _ (JSIdent "__IDRRT__Con")) check
      ) = removeHelper check
    removeHelper js = js


    eliminateDeadBranches ((JSTrue, cond):_) = [(JSNoop, cond)]
    eliminateDeadBranches [(_, js)]         = [(JSNoop, js)]
    eliminateDeadBranches (x:xs)            = x : eliminateDeadBranches xs
    eliminateDeadBranches []                = []


    removeNoopConds :: JS -> JS
    removeNoopConds (JSCond [(JSNoop, js)]) = js
    removeNoopConds js                      = js

removeInstanceChecks js = transformJS removeInstanceChecks js


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
                reducable js
                  | JSReturn ret   <- js = reducable ret
                  | JSNew _ args   <- js = and $ map reducable args
                  | JSArray fields <- js = and $ map reducable fields
                  | JSNum _        <- js = True
                  | JSNull         <- js = True
                  | JSIdent _      <- js = True
                  | otherwise            = False


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

        reduceCall funs js = transformJS (reduceCall funs) js


extractLocalConstructors :: [JS] -> [JS]
extractLocalConstructors js =
  concatMap extractLocalConstructors' js
  where
    globalCons :: [String]
    globalCons = concatMap (getGlobalCons) js


    extractLocalConstructors' :: JS -> [JS]
    extractLocalConstructors' js@(JSAlloc fun (Just (JSFunction args body))) =
      addCons cons [foldr (uncurry jsSubst) js (reverse cons)]
      where
        cons :: [(JS, JS)]
        cons = zipWith genName (foldJS match (++) [] body) [1..]
          where
            genName :: JS -> Int -> (JS, JS)
            genName js id =
              (js, JSIdent $ idrCTRNamespace ++ fun ++ "_" ++ show id)

            match :: JS -> [JS]
            match js
              | JSNew "__IDRRT__Con" args <- js
              , all isConstant args = [js]
              | otherwise           = []


        addCons :: [(JS, JS)] -> [JS] -> [JS]
        addCons [] js = js
        addCons (con@(_, name):cons) js
          | sum (map (countOccur name) js) > 0 =
              addCons cons ((allocCon con) : js)
          | otherwise =
              addCons cons js


        countOccur :: JS -> JS -> Int
        countOccur ident js = foldJS match (+) 0 js
          where
            match :: JS -> Int
            match js
              | js == ident = 1
              | otherwise   = 0


        allocCon :: (JS, JS) -> JS
        allocCon (js, JSIdent name) =
          JSAlloc name (Just js)


        isConstant :: JS -> Bool
        isConstant js
          | JSNew "__IDRRT__Con" args <- js
          , all isConstant args =
              True
          | otherwise =
              isJSConstantConstructor globalCons js

    extractLocalConstructors' js = [js]


    getGlobalCons :: JS -> [String]
    getGlobalCons js = foldJS match (++) [] js
      where
        match :: JS -> [String]
        match js
          | (JSAlloc name (Just (JSNew "__IDRRT__Con" _))) <- js =
              [name]
          | otherwise =
              []


evalCons :: [JS] -> [JS]
evalCons js =
  map (collapseCont . collapseTC . expandProj . evalCons') js
  where
    cons :: [(String, JS)]
    cons = concatMap getGlobalCons js

    evalCons' :: JS -> JS
    evalCons' js = transformJS match js
      where
        match :: JS -> JS
        match (JSApp (JSIdent "__IDRRT__EVALTC") [arg])
          | JSIdent name                     <- arg
          , Just (JSNew _ [_, JSNull, _, _]) <- lookupConstructor name cons =
              arg

        match (JSApp (JSIdent "__IDR__mEVAL0") [arg])
          | JSIdent name                     <- arg
          , Just (JSNew _ [_, JSNull, _, _]) <- lookupConstructor name cons =
              arg

        match js = transformJS match js


    lookupConstructor :: String -> [(String, JS)] -> Maybe JS
    lookupConstructor ctr cons
      | Just (JSIdent name)  <- lookup ctr cons = lookupConstructor name cons
      | Just con@(JSNew _ _) <- lookup ctr cons = Just con
      | otherwise                               = Nothing


    expandProj :: JS -> JS
    expandProj js = transformJS match js
      where
        match :: JS -> JS
        match (
            JSIndex (
              JSProj (JSIdent name) "vars"
            ) (
              JSNum (JSInt idx)
            )
          )
          | Just (JSNew _ [_, _, _, JSArray args]) <- lookup name cons =
              args !! idx

        match js = transformJS match js


    collapseTC :: JS -> JS
    collapseTC js = transformJS match js
      where
        match :: JS -> JS
        match (JSApp (JSIdent "__IDRRT__tailcall") [JSFunction [] (
            JSReturn (JSIdent name)
          )])
          | Just _ <- lookup name cons = (JSIdent name)

        match js = transformJS match js


    collapseCont :: JS -> JS
    collapseCont js = transformJS match js
      where
        match :: JS -> JS
        match (JSNew "__IDRRT__Cont" [JSFunction [] (
            JSReturn ret@(JSNew "__IDRRT__Cont" [JSFunction [] _])
          )]) = collapseCont ret


        match (JSNew "__IDRRT__Cont" [JSFunction [] (
            JSReturn (JSIdent name)
          )]) = JSIdent name

        match (JSNew "__IDRRT__Cont" [JSFunction [] (
            JSReturn ret@(JSNew "__IDRRT__Con" [_, _, _, JSArray args])
          )])
          | all collapsable args = ret
          where
            collapsable :: JS -> Bool
            collapsable (JSIdent _) = True
            collapsable js          = isJSConstantConstructor (map fst cons) js


        match js = transformJS match js


elimConds :: [JS] -> [JS]
elimConds js =
  let (conds, rest) = partition isCond js in
      foldl' eraseCond rest conds
  where
    isCond :: JS -> Bool
    isCond (JSAlloc
      fun (Just (JSFunction args (JSCond
          [ (JSBinOp "==" (JSNum (JSInt tag)) (JSProj (JSIdent _) "tag"), JSReturn t)
          , (JSNoop, JSReturn f)
          ])))
      )
      | isJSConstant t && isJSConstant f =
          True

      | JSIdent _ <- t
      , JSIdent _ <- f =
          True

    isCond (JSAlloc
      fun (Just (JSFunction args (JSCond
        [ (JSBinOp "==" (JSIdent _) c, JSReturn t)
        , (JSNoop, JSReturn f)
        ])))
      )
      | isJSConstant t && isJSConstant f && isJSConstant c =
          True

      | JSIdent _ <- t
      , JSIdent _ <- f
      , isJSConstant c =
          True

    isCond _ = False


    eraseCond :: [JS] -> JS -> [JS]
    eraseCond js (JSAlloc
      fun (Just (JSFunction args (JSCond
                  [ (c, JSReturn t)
                  , (_, JSReturn f)
                  ])
                )
      )) = map (inlineFunction fun args (JSTernary c t f)) js


removeUselessCons :: [JS] -> [JS]
removeUselessCons js =
  let (cons, rest) = partition isUseless js in
      foldl' eraseCon rest cons
  where
    isUseless :: JS -> Bool
    isUseless (JSAlloc fun (Just JSNull))      = True
    isUseless (JSAlloc fun (Just (JSIdent _))) = True
    isUseless _                                = False


    eraseCon :: [JS] -> JS -> [JS]
    eraseCon js (JSAlloc fun (Just val))  = map (jsSubst (JSIdent fun) val) js


getGlobalCons :: JS -> [(String, JS)]
getGlobalCons js = foldJS match (++) [] js
  where
    match :: JS -> [(String, JS)]
    match js
      | (JSAlloc name (Just con@(JSNew "__IDRRT__Con" _))) <- js =
          [(name, con)]
      | (JSAlloc name (Just con@(JSIdent _))) <- js =
          [(name, con)]
      | otherwise =
          []


getIncludes :: [FilePath] -> IO [String]
getIncludes = mapM readFile

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
  let (header, rt) = case target of
                               Node ->
                                 ("#!/usr/bin/env node\n", "-node")
                               JavaScript ->
                                 ("", "-browser")
  included   <- getIncludes includes
  path       <- (++) <$> getDataDir <*> (pure "/jsrts/")
  idrRuntime <- readFile $ path ++ "Runtime-common.js"
  tgtRuntime <- readFile $ concat [path, "Runtime", rt, ".js"]
  jsbn       <- readFile $ path ++ "jsbn/jsbn.js"
  writeFile filename $ header ++ (
      intercalate "\n" $ included ++ runtime jsbn idrRuntime tgtRuntime ++ functions
    )

  setPermissions filename (emptyPermissions { readable   = True
                                            , executable = target == Node
                                            , writable   = True
                                            })
  where
    def :: [(String, SDecl)]
    def = map (first translateNamespace) definitions


    checkForBigInt :: [JS] -> Bool
    checkForBigInt js = occur
      where
        occur :: Bool
        occur = or $ map (foldJS match (||) False) js

        match :: JS -> Bool
        match (JSIdent "__IDRRT__bigInt") = True
        match (JSWord (JSWord64 _))       = True
        match (JSNum (JSInteger _))       = True
        match js                          = False


    runtime :: String -> String -> String -> [String]
    runtime jsbn idrRuntime tgtRuntime =
      if checkForBigInt optimized
         then [jsbn, idrRuntime, tgtRuntime]
         else [idrRuntime, tgtRuntime]


    optimized :: [JS]
    optimized = translate >>> optimize $ def
      where
        translate p =
          prelude ++ concatMap translateDeclaration p ++ [mainLoop, invokeLoop]
        optimize p  =
          foldl' (flip ($)) p opt

        opt =
          [ removeEval
          , map inlineJS
          , removeIDs
          , reduceJS
          , map reduceConstants
          , initConstructors
          , map removeAllocations
          , elimDeadLoop
          , map elimDuplicateEvals
          , optimizeRuntimeCalls "__IDR__mEVAL0" "__IDRRT__EVALTC"
          , optimizeRuntimeCalls "__IDR__mAPPLY0" "__IDRRT__APPLYTC"
          , map removeInstanceChecks
          , inlineFunctions
          , map reduceContinuations
          , extractLocalConstructors
          , unfoldLookupTable
          , evalCons
          , elimConds
          , removeUselessCons
          ]

    functions :: [String]
    functions = map compileJS optimized

    prelude :: [JS]
    prelude =
      [ JSAnnotation JSConstructor $
          JSAlloc (idrRTNamespace ++ "Cont") (Just $ JSFunction ["k"] (
            JSAssign (JSProj JSThis "k") (JSIdent "k")
          ))
      , JSAnnotation JSConstructor $
          JSAlloc (idrRTNamespace ++ "Con") (Just $ JSFunction ["tag", "vars"] (
            JSSeq [ JSAssign (JSProj JSThis "tag") (JSIdent "tag")
                  , JSAssign (JSProj JSThis "vars") (JSIdent "vars")
                  ]
          ))
      ]

    mainLoop :: JS
    mainLoop =
        JSAlloc "main" $ Just $ JSFunction [] (
          case target of
              Node       -> mainFun
              JavaScript -> JSCond [ (exists document `jsAnd` isReady, mainFun)
                                   , (exists window, windowMainFun)
                                   , (JSTrue, mainFun)
                                   ]
      )
      where
        exists :: JS -> JS
        exists js = (JSPreOp "typeof " js) `jsNotEq` JSString "undefined"

        mainFun :: JS
        mainFun = jsTailcall $ jsCall runMain []

        window :: JS
        window = JSIdent "window"

        document :: JS
        document = JSIdent "document"

        windowMainFun :: JS
        windowMainFun = jsMeth window "addEventListener" [
            JSString "DOMContentLoaded"
            , JSFunction [] ( mainFun )
            , JSFalse
            ]

        isReady :: JS
        isReady = JSParens $ readyState `jsEq` JSString "complete" `jsOr` readyState `jsEq` JSString "loaded"

        readyState :: JS
        readyState = JSProj (JSIdent "document") "readyState"


        runMain :: String
        runMain = idrNamespace ++ translateName (sMN 0 "runMain")


    invokeLoop :: JS
    invokeLoop  = jsCall "main" []


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
translateConstant (Ch c)                   = JSString $ translateChar c
translateConstant (Str s)                  = JSString $ concatMap translateChar s
translateConstant (AType (ATInt ITNative)) = JSType JSIntTy
translateConstant StrType                  = JSType JSStringTy
translateConstant (AType (ATInt ITBig))    = JSType JSIntegerTy
translateConstant (AType ATFloat)          = JSType JSFloatTy
translateConstant (AType (ATInt ITChar))   = JSType JSCharTy
translateConstant PtrType                  = JSType JSPtrTy
translateConstant Forgot                   = JSType JSForgotTy
translateConstant (BI i)                   = jsBigInt $ JSString (show i)
translateConstant (B8 b)                   = JSWord (JSWord8 b)
translateConstant (B16 b)                  = JSWord (JSWord16 b)
translateConstant (B32 b)                  = JSWord (JSWord32 b)
translateConstant (B64 b)                  = JSWord (JSWord64 b)
translateConstant c =
  jsError $ "Unimplemented Constant: " ++ show c


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


translateDeclaration :: (String, SDecl) -> [JS]
translateDeclaration (path, SFun name params stackSize body)
  | (MN _ ap)             <- name
  , (SChkCase var cases) <- body
  , ap == txt "APPLY" =
      [ lookupTable "APPLY" [] var cases
      , jsDecl $ JSFunction ["mfn0", "marg0"] (JSReturn $
          JSTernary (
            (JSIdent "mfn0" `jsInstanceOf` jsCon) `jsAnd`
            (hasProp (idrLTNamespace ++ "APPLY") "mfn0")
          ) (JSApp
              (JSIndex
                (JSIdent (idrLTNamespace ++ "APPLY"))
                (JSProj (JSIdent "mfn0") "tag")
              )
              [JSIdent "mfn0", JSIdent "marg0"]
          ) JSNull
        )
      ]

  | (MN _ ev)            <- name
  , (SChkCase var cases) <- body
  , ev == txt "EVAL" =
      [ lookupTable "EVAL" [] var cases
      , jsDecl $ JSFunction ["marg0"] (JSReturn $
          JSTernary (
            (JSIdent "marg0" `jsInstanceOf` jsCon) `jsAnd`
            (hasProp (idrLTNamespace ++ "EVAL") "marg0")
          ) (JSApp
              (JSIndex
                (JSIdent (idrLTNamespace ++ "EVAL"))
                (JSProj (JSIdent "marg0") "tag")
              )
              [JSIdent "marg0"]
          ) (JSIdent "marg0")
        )
      ]
  | otherwise =
    let fun = translateExpression body in
        [jsDecl $ jsFun fun]

  where
    hasProp :: String -> String -> JS
    hasProp table var =
      JSIndex (JSIdent table) (JSProj (JSIdent var) "tag")


    caseFun :: [(LVar, String)] -> LVar -> SAlt -> JS
    caseFun aux var cse =
      let (JSReturn c) = translateCase (Just (translateVariableName var)) cse in
          jsFunAux aux c


    getTag :: SAlt -> Maybe Int
    getTag (SConCase _ tag _ _ _) = Just tag
    getTag _                      = Nothing


    lookupTable :: String -> [(LVar, String)] -> LVar -> [SAlt] -> JS
    lookupTable table aux var cases =
      JSAlloc (idrLTNamespace ++ table) $ Just (
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

  | (LZExt (ITFixed IT8) ITNative)  <- op = jsUnPackBits $ JSVar (last vars)
  | (LZExt (ITFixed IT16) ITNative) <- op = jsUnPackBits $ JSVar (last vars)
  | (LZExt (ITFixed IT32) ITNative) <- op = jsUnPackBits $ JSVar (last vars)

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

  | (LPlus (ATInt ITChar)) <- op
  , (lhs:rhs:_)            <- vars =
      jsCall "__IDRRT__fromCharCode" [
        JSBinOp "+" (
          jsCall "__IDRRT__charCode" [JSVar lhs]
        ) (
          jsCall "__IDRRT__charCode" [JSVar rhs]
        )
      ]

  | (LTrunc (ITFixed IT16) (ITFixed IT8)) <- op
  , (arg:_)                               <- vars =
      jsPackUBits8 (
        JSBinOp "&" (jsUnPackBits $ JSVar arg) (JSNum (JSInt 0xFF))
      )

  | (LTrunc (ITFixed IT32) (ITFixed IT16)) <- op
  , (arg:_)                                <- vars =
      jsPackUBits16 (
        JSBinOp "&" (jsUnPackBits $ JSVar arg) (JSNum (JSInt 0xFFFF))
      )

  | (LTrunc (ITFixed IT64) (ITFixed IT32)) <- op
  , (arg:_)                                <- vars =
      jsPackUBits32 (
        jsMeth (jsMeth (JSVar arg) "and" [
          jsBigInt (JSString $ show 0xFFFFFFFF)
        ]) "intValue" []
      )

  | (LTrunc ITBig (ITFixed IT64)) <- op
  , (arg:_)                       <- vars =
      jsMeth (JSVar arg) "and" [
        jsBigInt (JSString $ show 0xFFFFFFFFFFFFFFFF)
      ]

  | (LLSHR (ITFixed IT8)) <- op
  , (lhs:rhs:_)           <- vars =
      jsPackUBits8 (
        JSBinOp ">>" (jsUnPackBits $ JSVar lhs) (jsUnPackBits $ JSVar rhs)
      )

  | (LLSHR (ITFixed IT16)) <- op
  , (lhs:rhs:_)            <- vars =
      jsPackUBits16 (
        JSBinOp ">>" (jsUnPackBits $ JSVar lhs) (jsUnPackBits $ JSVar rhs)
      )

  | (LLSHR (ITFixed IT32)) <- op
  , (lhs:rhs:_)            <- vars =
      jsPackUBits32  (
        JSBinOp ">>" (jsUnPackBits $ JSVar lhs) (jsUnPackBits $ JSVar rhs)
      )

  | (LLSHR (ITFixed IT64)) <- op
  , (lhs:rhs:_)            <- vars =
      jsMeth (JSVar lhs) "shiftRight" [JSVar rhs]

  | (LSHL (ITFixed IT8)) <- op
  , (lhs:rhs:_)          <- vars =
      jsPackUBits8 (
        JSBinOp "<<" (jsUnPackBits $ JSVar lhs) (jsUnPackBits $ JSVar rhs)
      )

  | (LSHL (ITFixed IT16)) <- op
  , (lhs:rhs:_)           <- vars =
      jsPackUBits16 (
        JSBinOp "<<" (jsUnPackBits $ JSVar lhs) (jsUnPackBits $ JSVar rhs)
      )

  | (LSHL (ITFixed IT32)) <- op
  , (lhs:rhs:_)           <- vars =
      jsPackUBits32  (
        JSBinOp "<<" (jsUnPackBits $ JSVar lhs) (jsUnPackBits $ JSVar rhs)
      )

  | (LSHL (ITFixed IT64)) <- op
  , (lhs:rhs:_)           <- vars =
      jsMeth (jsMeth (JSVar lhs) "shiftLeft" [JSVar rhs]) "and" [
        jsBigInt (JSString $ show 0xFFFFFFFFFFFFFFFF)
      ]

  | (LAnd (ITFixed IT8)) <- op
  , (lhs:rhs:_)          <- vars =
      jsPackUBits8 (
        JSBinOp "&" (jsUnPackBits (JSVar lhs)) (jsUnPackBits (JSVar rhs))
      )

  | (LAnd (ITFixed IT16)) <- op
  , (lhs:rhs:_)           <- vars =
      jsPackUBits16 (
        JSBinOp "&" (jsUnPackBits (JSVar lhs)) (jsUnPackBits (JSVar rhs))
      )

  | (LAnd (ITFixed IT32)) <- op
  , (lhs:rhs:_)           <- vars =
      jsPackUBits32 (
        JSBinOp "&" (jsUnPackBits (JSVar lhs)) (jsUnPackBits (JSVar rhs))
      )

  | (LAnd (ITFixed IT64)) <- op
  , (lhs:rhs:_)           <- vars =
      jsMeth (JSVar lhs) "and" [JSVar rhs]

  | (LOr (ITFixed IT8)) <- op
  , (lhs:rhs:_)         <- vars =
      jsPackUBits8 (
        JSBinOp "|" (jsUnPackBits (JSVar lhs)) (jsUnPackBits (JSVar rhs))
      )

  | (LOr (ITFixed IT16)) <- op
  , (lhs:rhs:_)          <- vars =
      jsPackUBits16 (
        JSBinOp "|" (jsUnPackBits (JSVar lhs)) (jsUnPackBits (JSVar rhs))
      )

  | (LOr (ITFixed IT32)) <- op
  , (lhs:rhs:_)          <- vars =
      jsPackUBits32 (
        JSBinOp "|" (jsUnPackBits (JSVar lhs)) (jsUnPackBits (JSVar rhs))
      )

  | (LOr (ITFixed IT64)) <- op
  , (lhs:rhs:_)          <- vars =
      jsMeth (JSVar lhs) "or" [JSVar rhs]

  | (LXOr (ITFixed IT8)) <- op
  , (lhs:rhs:_)          <- vars =
      jsPackUBits8 (
        JSBinOp "^" (jsUnPackBits (JSVar lhs)) (jsUnPackBits (JSVar rhs))
      )

  | (LXOr (ITFixed IT16)) <- op
  , (lhs:rhs:_)           <- vars =
      jsPackUBits16 (
        JSBinOp "^" (jsUnPackBits (JSVar lhs)) (jsUnPackBits (JSVar rhs))
      )

  | (LXOr (ITFixed IT32)) <- op
  , (lhs:rhs:_)           <- vars =
      jsPackUBits32 (
        JSBinOp "^" (jsUnPackBits (JSVar lhs)) (jsUnPackBits (JSVar rhs))
      )

  | (LXOr (ITFixed IT64)) <- op
  , (lhs:rhs:_)           <- vars =
      jsMeth (JSVar lhs) "xor" [JSVar rhs]

  | (LPlus (ATInt (ITFixed IT8))) <- op
  , (lhs:rhs:_)                   <- vars =
      jsPackUBits8 (
        JSBinOp "+" (jsUnPackBits (JSVar lhs)) (jsUnPackBits (JSVar rhs))
      )

  | (LPlus (ATInt (ITFixed IT16))) <- op
  , (lhs:rhs:_)                    <- vars =
      jsPackUBits16 (
        JSBinOp "+" (jsUnPackBits (JSVar lhs)) (jsUnPackBits (JSVar rhs))
      )

  | (LPlus (ATInt (ITFixed IT32))) <- op
  , (lhs:rhs:_)                    <- vars =
      jsPackUBits32 (
        JSBinOp "+" (jsUnPackBits (JSVar lhs)) (jsUnPackBits (JSVar rhs))
      )

  | (LPlus (ATInt (ITFixed IT64))) <- op
  , (lhs:rhs:_)                    <- vars =
      jsMeth (jsMeth (JSVar lhs) "add" [JSVar rhs]) "and" [
        jsBigInt (JSString $ show 0xFFFFFFFFFFFFFFFF)
      ]

  | (LMinus (ATInt (ITFixed IT8))) <- op
  , (lhs:rhs:_)                    <- vars =
      jsPackUBits8 (
        JSBinOp "-" (jsUnPackBits (JSVar lhs)) (jsUnPackBits (JSVar rhs))
      )

  | (LMinus (ATInt (ITFixed IT16))) <- op
  , (lhs:rhs:_)                     <- vars =
      jsPackUBits16 (
        JSBinOp "-" (jsUnPackBits (JSVar lhs)) (jsUnPackBits (JSVar rhs))
      )

  | (LMinus (ATInt (ITFixed IT32))) <- op
  , (lhs:rhs:_)                     <- vars =
      jsPackUBits32 (
        JSBinOp "-" (jsUnPackBits (JSVar lhs)) (jsUnPackBits (JSVar rhs))
      )

  | (LMinus (ATInt (ITFixed IT64))) <- op
  , (lhs:rhs:_)                     <- vars =
      jsMeth (jsMeth (JSVar lhs) "subtract" [JSVar rhs]) "and" [
        jsBigInt (JSString $ show 0xFFFFFFFFFFFFFFFF)
      ]

  | (LTimes (ATInt (ITFixed IT8))) <- op
  , (lhs:rhs:_)                    <- vars =
      jsPackUBits8 (
        JSBinOp "*" (jsUnPackBits (JSVar lhs)) (jsUnPackBits (JSVar rhs))
      )

  | (LTimes (ATInt (ITFixed IT16))) <- op
  , (lhs:rhs:_)                     <- vars =
      jsPackUBits16 (
        JSBinOp "*" (jsUnPackBits (JSVar lhs)) (jsUnPackBits (JSVar rhs))
      )

  | (LTimes (ATInt (ITFixed IT32))) <- op
  , (lhs:rhs:_)                     <- vars =
      jsPackUBits32 (
        JSBinOp "*" (jsUnPackBits (JSVar lhs)) (jsUnPackBits (JSVar rhs))
      )

  | (LTimes (ATInt (ITFixed IT64))) <- op
  , (lhs:rhs:_)                     <- vars =
      jsMeth (jsMeth (JSVar lhs) "multiply" [JSVar rhs]) "and" [
        jsBigInt (JSString $ show 0xFFFFFFFFFFFFFFFF)
      ]

  | (LEq (ATInt (ITFixed IT8))) <- op
  , (lhs:rhs:_)                 <- vars =
      jsPackUBits8 (
        JSBinOp "==" (jsUnPackBits (JSVar lhs)) (jsUnPackBits (JSVar rhs))
      )

  | (LEq (ATInt (ITFixed IT16))) <- op
  , (lhs:rhs:_)                  <- vars =
      jsPackUBits16 (
        JSBinOp "==" (jsUnPackBits (JSVar lhs)) (jsUnPackBits (JSVar rhs))
      )

  | (LEq (ATInt (ITFixed IT32))) <- op
  , (lhs:rhs:_)                  <- vars =
      jsPackUBits32 (
        JSBinOp "==" (jsUnPackBits (JSVar lhs)) (jsUnPackBits (JSVar rhs))
      )

  | (LEq (ATInt (ITFixed IT64))) <- op
  , (lhs:rhs:_)                   <- vars =
      jsMeth (jsMeth (JSVar lhs) "equals" [JSVar rhs]) "and" [
        jsBigInt (JSString $ show 0xFFFFFFFFFFFFFFFF)
      ]

  | (LLt (ITFixed IT8)) <- op
  , (lhs:rhs:_)         <- vars =
      jsPackUBits8 (
        JSBinOp "<" (jsUnPackBits (JSVar lhs)) (jsUnPackBits (JSVar rhs))
      )

  | (LLt (ITFixed IT16)) <- op
  , (lhs:rhs:_)          <- vars =
      jsPackUBits16 (
        JSBinOp "<" (jsUnPackBits (JSVar lhs)) (jsUnPackBits (JSVar rhs))
      )

  | (LLt (ITFixed IT32)) <- op
  , (lhs:rhs:_)          <- vars =
      jsPackUBits32 (
        JSBinOp "<" (jsUnPackBits (JSVar lhs)) (jsUnPackBits (JSVar rhs))
      )

  | (LLt (ITFixed IT64)) <- op
  , (lhs:rhs:_)          <- vars = invokeMeth lhs "lesser" [rhs]

  | (LLe (ITFixed IT8)) <- op
  , (lhs:rhs:_)         <- vars =
      jsPackUBits8 (
        JSBinOp "<=" (jsUnPackBits (JSVar lhs)) (jsUnPackBits (JSVar rhs))
      )

  | (LLe (ITFixed IT16)) <- op
  , (lhs:rhs:_)          <- vars =
      jsPackUBits16 (
        JSBinOp "<=" (jsUnPackBits (JSVar lhs)) (jsUnPackBits (JSVar rhs))
      )

  | (LLe (ITFixed IT32)) <- op
  , (lhs:rhs:_)          <- vars =
      jsPackUBits32 (
        JSBinOp "<=" (jsUnPackBits (JSVar lhs)) (jsUnPackBits (JSVar rhs))
      )

  | (LLe (ITFixed IT64)) <- op
  , (lhs:rhs:_)          <- vars = invokeMeth lhs "lesserOrEquals" [rhs]

  | (LGt (ITFixed IT8)) <- op
  , (lhs:rhs:_)         <- vars =
      jsPackUBits8 (
        JSBinOp ">" (jsUnPackBits (JSVar lhs)) (jsUnPackBits (JSVar rhs))
      )

  | (LGt (ITFixed IT16)) <- op
  , (lhs:rhs:_)          <- vars =
      jsPackUBits16 (
        JSBinOp ">" (jsUnPackBits (JSVar lhs)) (jsUnPackBits (JSVar rhs))
      )
  | (LGt (ITFixed IT32)) <- op
  , (lhs:rhs:_)          <- vars =
      jsPackUBits32 (
        JSBinOp ">" (jsUnPackBits (JSVar lhs)) (jsUnPackBits (JSVar rhs))
      )

  | (LGt (ITFixed IT64)) <- op
  , (lhs:rhs:_)          <- vars = invokeMeth lhs "greater" [rhs]

  | (LGe (ITFixed IT8)) <- op
  , (lhs:rhs:_)         <- vars =
      jsPackUBits8 (
        JSBinOp ">=" (jsUnPackBits (JSVar lhs)) (jsUnPackBits (JSVar rhs))
      )

  | (LGe (ITFixed IT16)) <- op
  , (lhs:rhs:_)          <- vars =
      jsPackUBits16 (
        JSBinOp ">=" (jsUnPackBits (JSVar lhs)) (jsUnPackBits (JSVar rhs))
      )
  | (LGe (ITFixed IT32)) <- op
  , (lhs:rhs:_)          <- vars =
      jsPackUBits32 (
        JSBinOp ">=" (jsUnPackBits (JSVar lhs)) (jsUnPackBits (JSVar rhs))
      )

  | (LGe (ITFixed IT64)) <- op
  , (lhs:rhs:_)          <- vars = invokeMeth lhs "greaterOrEquals" [rhs]

  | (LUDiv (ITFixed IT8)) <- op
  , (lhs:rhs:_)           <- vars =
      jsPackUBits8 (
        JSBinOp "/" (jsUnPackBits (JSVar lhs)) (jsUnPackBits (JSVar rhs))
      )

  | (LUDiv (ITFixed IT16)) <- op
  , (lhs:rhs:_)            <- vars =
      jsPackUBits16 (
        JSBinOp "/" (jsUnPackBits (JSVar lhs)) (jsUnPackBits (JSVar rhs))
      )

  | (LUDiv (ITFixed IT32)) <- op
  , (lhs:rhs:_)            <- vars =
      jsPackUBits32 (
        JSBinOp "/" (jsUnPackBits (JSVar lhs)) (jsUnPackBits (JSVar rhs))
      )

  | (LUDiv (ITFixed IT64)) <- op
  , (lhs:rhs:_)            <- vars = invokeMeth lhs "divide" [rhs]

  | (LSDiv (ATInt (ITFixed IT8))) <- op
  , (lhs:rhs:_)                   <- vars =
      jsPackSBits8 (
        JSBinOp "/" (
          jsUnPackBits $ jsPackSBits8 $ jsUnPackBits (JSVar lhs)
        ) (
          jsUnPackBits $ jsPackSBits8 $ jsUnPackBits (JSVar rhs)
        )
      )

  | (LSDiv (ATInt (ITFixed IT16))) <- op
  , (lhs:rhs:_)                    <- vars =
      jsPackSBits16 (
        JSBinOp "/" (
          jsUnPackBits $ jsPackSBits16 $ jsUnPackBits (JSVar lhs)
        ) (
          jsUnPackBits $ jsPackSBits16 $ jsUnPackBits (JSVar rhs)
        )
      )

  | (LSDiv (ATInt (ITFixed IT32))) <- op
  , (lhs:rhs:_)                    <- vars =
      jsPackSBits32 (
        JSBinOp "/" (
          jsUnPackBits $ jsPackSBits32 $ jsUnPackBits (JSVar lhs)
        ) (
          jsUnPackBits $ jsPackSBits32 $ jsUnPackBits (JSVar rhs)
        )
      )

  | (LSDiv (ATInt (ITFixed IT64))) <- op
  , (lhs:rhs:_)                    <- vars = invokeMeth lhs "divide" [rhs]

  | (LSRem (ATInt (ITFixed IT8))) <- op
  , (lhs:rhs:_)                   <- vars =
      jsPackSBits8 (
        JSBinOp "%" (
          jsUnPackBits $ jsPackSBits8 $ jsUnPackBits (JSVar lhs)
        ) (
          jsUnPackBits $ jsPackSBits8 $ jsUnPackBits (JSVar rhs)
        )
      )

  | (LSRem (ATInt (ITFixed IT16))) <- op
  , (lhs:rhs:_)                    <- vars =
      jsPackSBits16 (
        JSBinOp "%" (
          jsUnPackBits $ jsPackSBits16 $ jsUnPackBits (JSVar lhs)
        ) (
          jsUnPackBits $ jsPackSBits16 $ jsUnPackBits (JSVar rhs)
        )
      )

  | (LSRem (ATInt (ITFixed IT32))) <- op
  , (lhs:rhs:_)                    <- vars =
      jsPackSBits32 (
        JSBinOp "%" (
          jsUnPackBits $ jsPackSBits32 $ jsUnPackBits (JSVar lhs)
        ) (
          jsUnPackBits $ jsPackSBits32 $ jsUnPackBits (JSVar rhs)
        )
      )

  | (LSRem (ATInt (ITFixed IT64))) <- op
  , (lhs:rhs:_)                    <- vars = invokeMeth lhs "mod" [rhs]

  | (LCompl (ITFixed IT8)) <- op
  , (arg:_)                <- vars =
      jsPackSBits8 $ JSPreOp "~" $ jsUnPackBits (JSVar arg)

  | (LCompl (ITFixed IT16)) <- op
  , (arg:_)                 <- vars =
      jsPackSBits16 $ JSPreOp "~" $ jsUnPackBits (JSVar arg)

  | (LCompl (ITFixed IT32)) <- op
  , (arg:_)                 <- vars =
      jsPackSBits32 $ JSPreOp "~" $ jsUnPackBits (JSVar arg)

  | (LCompl (ITFixed IT64)) <- op
  , (arg:_)     <- vars =
      invokeMeth arg "not" []

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
  , (arg:_)     <- vars = JSPreOp "~" (JSVar arg)

  | LStrConcat  <- op
  , (lhs:rhs:_) <- vars = invokeMeth lhs "concat" [rhs]
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
  , (arg:_)                 <- vars = jsCall "__IDRRT__charCode" [JSVar arg]
  | (LIntCh ITNative)       <- op
  , (arg:_)                 <- vars = jsCall "__IDRRT__fromCharCode" [JSVar arg]

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
  , (lhs:rhs:_) <- vars = invokeMeth lhs "concat" [rhs]
  | LStrHead    <- op
  , (arg:_)     <- vars = JSIndex (JSVar arg) (JSNum (JSInt 0))
  | LStrRev     <- op
  , (arg:_)     <- vars = JSProj (JSVar arg) "split('').reverse().join('')"
  | LStrIndex   <- op
  , (lhs:rhs:_) <- vars = JSIndex (JSVar lhs) (JSVar rhs)
  | LStrTail    <- op
  , (arg:_)     <- vars = let v = translateVariableName arg in
                              JSApp (JSProj (JSIdent v) "substr") [
                                JSNum (JSInt 1),
                                JSBinOp "-" (JSProj (JSIdent v) "length") (JSNum (JSInt 1))
                              ]
  | LSystemInfo <- op
  , (arg:_) <- vars = jsCall "__IDRRT__systemInfo"  [JSVar arg]
  | LNullPtr    <- op
  , (_)         <- vars = JSNull

  where
    translateBinaryOp :: String -> LVar -> LVar -> JS
    translateBinaryOp f lhs rhs = JSParens $ JSBinOp f (JSVar lhs) (JSVar rhs)


    invokeMeth :: LVar -> String -> [LVar] -> JS
    invokeMeth obj meth args = jsMeth (JSVar obj) meth (map JSVar args)

translateExpression (SError msg) =
  jsError msg

translateExpression (SForeign _ _ "putStr" [(FString, var)]) =
  jsCall (idrRTNamespace ++ "print") [JSVar var]

translateExpression (SForeign _ _ "isNull" [(FPtr, var)]) =
  JSBinOp "==" (JSVar var) JSNull

translateExpression (SForeign _ _ "idris_eqPtr" [(FPtr, lhs),(FPtr, rhs)]) =
  JSBinOp "==" (JSVar lhs) (JSVar rhs)

translateExpression (SForeign _ _ "idris_time" []) =
  JSRaw "(new Date()).getTime()"

translateExpression (SForeign _ _ fun args) =
  JSFFI fun (map generateWrapper args)
  where
    generateWrapper (ffunc, name)
      | FFunction   <- ffunc =
          JSApp (
            JSIdent $ idrRTNamespace ++ "ffiWrap"
          ) [JSIdent $ translateVariableName name]
      | FFunctionIO <- ffunc =
          JSApp (
            JSIdent $ idrRTNamespace ++ "ffiWrap"
          ) [JSIdent $ translateVariableName name]

    generateWrapper (_, name) =
      JSIdent $ translateVariableName name

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
  jsError $ "Not yet implemented: " ++ filter (/= '\'') (show e)


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
translateCase _          (SDefaultCase e) = JSReturn $ translateExpression e
translateCase _          (SConstCase _ e) = JSReturn $ translateExpression e
translateCase (Just var) (SConCase a _ _ vars e) =
  let params = map jsVar [a .. (a + length vars)] in
      JSReturn $ jsMeth (JSFunction params (JSReturn $ translateExpression e)) "apply" [
        JSThis, JSProj (JSIdent var) "vars"
      ]
