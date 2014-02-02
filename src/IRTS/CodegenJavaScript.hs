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
        | JSString String
        | JSChar String
        | JSNum JSNum
        | JSAssign JS JS
        | JSAlloc String (Maybe JS)
        | JSIndex JS JS
        | JSCond [(JS, JS)]
        | JSTernary JS JS JS
        | JSParens JS
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
  "throw new Error(\"" ++ exc ++ "\")"

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
  intercalate " else " $ map createIfBlock branches
  where
    createIfBlock (JSTrue, e) =
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


jsError :: String -> JS
jsError err = JSApp (JSFunction [] (JSError err)) []


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
      | JSOp _ lhs rhs       <- js =
          add (tr js) $ add (fold lhs) (fold rhs)
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
      | JSOp op lhs rhs      <- js = JSOp op (tr lhs) (tr rhs)
      | JSProj obj field     <- js = JSProj (tr obj) field
      | JSArray vals         <- js = JSArray $ map tr vals
      | JSAssign lhs rhs     <- js = JSAssign (tr lhs) (tr rhs)
      | JSAlloc var val      <- js = JSAlloc var $ fmap tr val
      | JSIndex lhs rhs      <- js = JSIndex (tr lhs) (tr rhs)
      | JSCond conds         <- js = JSCond $ map (tr *** tr) conds
      | JSTernary c t f      <- js = JSTernary (tr c) (tr t) (tr f)
      | JSParens val         <- js = JSParens $ tr val
      | otherwise                  = js


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
  | JSString _ <- js = True
  | JSChar _   <- js = True
  | JSNum _    <- js = True
  | JSType _   <- js = True
  | JSNull     <- js = True

  | JSApp (JSIdent "__IDRRT__bigInt") _ <- js = True
  | otherwise = False


inlineJS :: JS -> JS
inlineJS (JSReturn (JSApp (JSFunction [] err@(JSError _)) [])) = err
inlineJS (JSReturn (JSApp (JSFunction ["cse"] body) [val@(JSVar _)])) =
  inlineJS $ jsSubst (JSIdent "cse") val body


inlineJS (JSReturn (JSApp (JSFunction [arg] cond@(JSCond _)) [val])) =
  inlineJS $ JSSeq [ JSAlloc arg (Just val)
                   , cond
                   ]

inlineJS (JSApp (JSProj (JSFunction args (JSReturn body)) "apply") [
    JSThis,JSProj var "vars"
  ])
  | var /= JSIdent "cse" =
      inlineJS $ inlineApply args body 0
  where
    inlineApply []     body _ = inlineJS body
    inlineApply (a:as) body n =
      inlineApply as (
        jsSubst (JSIdent a) (JSIndex (JSProj var "vars") (JSNum (JSInt n))) body
      ) (n + 1)

inlineJS (JSApp (JSIdent "__IDR__mEVAL0") [val])
  | isJSConstant val = val

inlineJS (JSApp (JSIdent "__IDRRT__tailcall") [
    JSFunction [] (JSReturn val)
  ])
  | isJSConstant val = val

inlineJS (JSApp (JSFunction [arg] (JSReturn ret)) [val])
  | JSNew con [tag, vals] <- ret
  , opt <- inlineJS val =
      inlineJS $ JSNew con [tag, inlineJS $ jsSubst (JSIdent arg) opt vals]

  | JSNew con [JSFunction [] (JSReturn (JSApp fun vars))] <- ret
  , opt <- inlineJS val =
      inlineJS $ JSNew con [JSFunction [] (
        JSReturn (
          JSApp (
            inlineJS $ jsSubst (JSIdent arg) opt fun
          ) (
            map (inlineJS . jsSubst (JSIdent arg) opt) vars
          )
        )
      )]

  | JSApp (JSProj obj field) args <- ret
  , opt <- inlineJS val =
      inlineJS $ JSApp (
        inlineJS $ JSProj (jsSubst (JSIdent arg) opt obj) field
      ) (
        map (inlineJS . jsSubst (JSIdent arg) opt) args
      )

  | JSIndex (JSProj obj field) idx <- ret
  , opt <- inlineJS val =
      inlineJS $ JSIndex (JSProj (
          inlineJS $ jsSubst (JSIdent arg) opt obj
        ) field
      ) (inlineJS $ jsSubst (JSIdent arg) opt idx)

  | JSOp op lhs rhs <- ret
  , opt <- inlineJS val =
      inlineJS $ JSOp op (inlineJS $ jsSubst (JSIdent arg) opt lhs) $
        (inlineJS $ jsSubst (JSIdent arg) opt rhs)

  | JSApp (JSIdent fun) args <- ret
  , opt <- inlineJS val =
      inlineJS $ JSApp (JSIdent fun) $ map (inlineJS . jsSubst (JSIdent arg) opt) args

inlineJS js = transformJS inlineJS js


reduceJS :: [JS] -> [JS]
reduceJS js = reduceLoop [] ([], js)


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
      map createConstant tags ++ replaceConstructors tags js
      where
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
              | tag `elem` tags = JSIdent ("__IDRCTR__" ++ show tag)

            replaceHelper tags js = transformJS (replaceHelper tags) js


        createConstant :: Int -> JS
        createConstant tag =
          JSAlloc ("__IDRCTR__" ++ show tag) (Just (
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
          , pos < length args  = args !! pos

        removeIDCall ids (JSNew _ [JSFunction [] (
                           JSReturn (JSApp (JSIdent fun) args)
                         )])
          | Just pos <- lookup fun ids
          , pos < length args = args !! pos

        removeIDCall ids js@(JSApp id@(JSIdent fun) args)
          | Just pos <- lookup fun ids
          , pos < length args  = args !! pos

        removeIDCall ids js = transformJS (removeIDCall ids) js


inlineFunctions :: [JS] -> [JS]
inlineFunctions js =
  inlineHelper ([], js)
  where
    inlineHelper :: ([JS], [JS]) -> [JS]
    inlineHelper (front , (JSAlloc fun (Just (JSFunction  args body))):back)
      | countAll fun front + countAll fun back == 0 =
         inlineHelper (front, back)
      | Just new <- inlineAble (
            countAll fun front + countAll fun back
          ) fun args body =
              let f = map (inline fun args new) in
                  inlineHelper (f front, f back)

    inlineHelper (front, next:back) = inlineHelper (front ++ [next], back)
    inlineHelper (front, [])        = front


    inlineAble :: Int -> String -> [String] -> JS -> Maybe JS
    inlineAble 1 fun args body
      | nonRecur fun body =
          inlineAble' body
            where
              inlineAble' :: JS -> Maybe JS
              inlineAble' (
                  JSReturn js@(JSNew "__IDRRT__Con" [JSNum _, JSArray vals])
                )
                | and $ map (\x -> isJSIdent x || isJSConstant x) vals = Just js

              inlineAble' (
                  JSReturn js@(JSNew "__IDRRT__Cont" [JSFunction [] (
                    JSReturn (JSApp (JSIdent _) args)
                  )])
                )
                | and $ map (\x -> isJSIdent x || isJSConstant x) args = Just js

              inlineAble' (
                  JSReturn js@(JSIndex (JSProj (JSApp (JSIdent _) args) "vars") _)
                )
                | and $ map (\x -> isJSIdent x || isJSConstant x) args = Just js

              inlineAble' _ = Nothing

              isJSIdent js
                | JSIdent _ <- js = True
                | otherwise       = False

    inlineAble _ _ _ _ = Nothing


    inline :: String -> [String] -> JS -> JS -> JS
    inline fun args body js = inline' js
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


    nonRecur :: String -> JS -> Bool
    nonRecur name body = countInvokations name body == 0


    countAll :: String -> [JS] -> Int
    countAll name js = sum $ map (countInvokations name) js


    countInvokations :: String -> JS -> Int
    countInvokations name = foldJS match (+) 0
      where
        match :: JS -> Int
        match js
          | JSApp (JSIdent ident) _ <- js
          , name == ident = 1
          | otherwise     = 0


reduceContinuations :: JS -> JS
reduceContinuations = transformJS reduceHelper
  where
    reduceHelper :: JS -> JS
    reduceHelper (JSNew "__IDRRT__Cont" [JSFunction [] (
        JSReturn js@(JSNew "__IDRRT__Cont" [JSFunction [] body])
      )]) = js

    reduceHelper js = transformJS reduceHelper js


reduceConstant :: JS -> JS
reduceConstant
  (JSApp (JSIdent "__IDRRT__tailcall") [JSFunction [] (
    JSReturn (JSApp (JSIdent "__IDR__mEVAL0") [val])
  )])
  | JSNum num       <- val = val
  | JSOp op lhs rhs <- val =
      JSParens $ JSOp op (reduceConstant lhs) (reduceConstant rhs)

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


optimizeEvalTailcalls :: (String, String) -> JS -> JS
optimizeEvalTailcalls (fun, tc) js =
  optHelper js
  where
    optHelper :: JS -> JS
    optHelper (JSApp (JSIdent "__IDRRT__tailcall") [
        JSFunction [] (JSReturn (JSApp (JSIdent n) args))
      ])
      | n == fun = JSApp (JSIdent tc) $ map optHelper args

    optHelper js = transformJS optHelper js


removeInstanceChecks :: JS -> JS
removeInstanceChecks (JSCond conds) =
  JSCond $ eliminateDeadBranches $ map (
    removeHelper *** removeInstanceChecks
  ) conds
  where
    removeHelper (
        JSOp "&&" (JSOp "instanceof" _ (JSIdent "__IDRRT__Con")) check
      ) = removeHelper check
    removeHelper js = js


    eliminateDeadBranches (e@(JSTrue, _):_) = [e]
    eliminateDeadBranches [(_, js)]         = [(JSTrue, js)]
    eliminateDeadBranches (x:xs)            = x : eliminateDeadBranches xs
    eliminateDeadBranches []                = []

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
                       ] ++ functions
    )

  setPermissions filename (emptyPermissions { readable   = True
                                            , executable = target == Node
                                            , writable   = True
                                            })
  where
    def :: [(String, SDecl)]
    def = map (first translateNamespace) definitions


    functions :: [String]
    functions = translate >>> optimize >>> compile $ def
      where
        translate p = concatMap translateDeclaration p ++ [mainLoop, invokeLoop]
        optimize p  = foldl' (flip ($)) p opt
        compile     = map compileJS

        opt =
          [ map optimizeJS
          , removeIDs
          , reduceJS
          , map reduceConstants
          , initConstructors
          , map removeAllocations
          , elimDeadLoop
          , map elimDuplicateEvals
          , map (optimizeEvalTailcalls ("__IDR__mEVAL0", "__IDRRT__EVALTC"))
          , map (optimizeEvalTailcalls ("__IDR__mAPPLY0", "__IDRRT__APPLYTC"))
          , map removeInstanceChecks
          , inlineFunctions
          , map reduceContinuations
          ]


    mainLoop :: JS
    mainLoop =
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
  jsError $ "Unimplemented Constant: " ++ show c


translateDeclaration :: (String, SDecl) -> [JS]
translateDeclaration (path, SFun name params stackSize body)
  | (MN _ ap)             <- name
  , (SLet var val next)   <- body
  , (SChkCase cvar cases) <- next
  , ap == txt "APPLY" =
    let lvar   = translateVariableName var
        lookup = "[" ++ lvar ++ ".tag](fn0,arg0," ++ lvar ++ ")" in
        [ lookupTable [(var, "chk")] var cases
        , jsDecl $ JSFunction ["fn0", "arg0"] (
            JSSeq [ JSAlloc "__var_0" (Just $ JSIdent "fn0")
                  , JSAlloc (translateVariableName var) (
                      Just $ translateExpression val
                    )
                  , JSReturn $ (JSTernary (
                       (JSVar var `jsInstanceOf` jsCon) `jsAnd`
                       (hasProp lookupTableName (translateVariableName var))
                    ) (JSIdent $
                         lookupTableName ++ lookup
                      ) JSNull
                    )
                  ]
          )
        ]

  | (MN _ ev)            <- name
  , (SChkCase var cases) <- body
  , ev == txt "EVAL" =
    [ lookupTable [] var cases
    , jsDecl $ JSFunction ["arg0"] (JSReturn $
        JSTernary (
          (JSIdent "arg0" `jsInstanceOf` jsCon) `jsAnd`
          (hasProp lookupTableName "arg0")
        ) (JSApp
            (JSIndex (JSIdent lookupTableName) (JSProj (JSIdent "arg0") "tag"))
            [JSIdent "arg0"]
        ) (JSIdent "arg0")
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
  jsError msg

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
  jsError $ "Not yet implemented: " ++ filter (/= '\'') (show e)


data FFI = FFICode Char | FFIArg Int | FFIError String


ffi :: String -> [String] -> JS
ffi code args = let parsed = ffiParse code in
                    case ffiError parsed of
                         Just err -> jsError err
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
translateCase _          (SDefaultCase e) = JSReturn $ translateExpression e
translateCase _          (SConstCase _ e) = JSReturn $ translateExpression e
translateCase (Just var) (SConCase a _ _ vars e) =
  let params = map jsVar [a .. (a + length vars)] in
      JSReturn $ jsMeth (JSFunction params (JSReturn $ translateExpression e)) "apply" [
        JSThis, JSProj (JSIdent var) "vars"
      ]
