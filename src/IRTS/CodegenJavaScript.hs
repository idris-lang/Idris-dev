{-|
Module      : IRTS.CodegenJavaScript
Description : The JavaScript code generator.
Copyright   :
License     : BSD3
Maintainer  : The Idris Community.
-}
{-# LANGUAGE OverloadedStrings, PatternGuards #-}
module IRTS.CodegenJavaScript (codegenJavaScript
                             , codegenNode
                             , JSTarget(..)
                             ) where

import Idris.AbsSyntax hiding (TypeCase)
import Idris.Core.TT
import IRTS.Bytecode
import IRTS.CodegenCommon
import IRTS.Defunctionalise
import IRTS.Exports
import IRTS.JavaScript.AST
import IRTS.Lang
import IRTS.Simplified
import IRTS.System
import Util.System

import Control.Applicative (pure, (<$>), (<*>))
import Control.Arrow
import Control.Monad (mapM)
import Control.Monad.RWS hiding (mapM)
import Control.Monad.State
import Data.Char
import Data.List
import qualified Data.Map.Strict as M
import Data.Maybe
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import Data.Traversable hiding (mapM)
import Data.Word
import Numeric
import System.Directory
import System.FilePath
import System.IO


data CompileInfo = CompileInfo { compileInfoApplyCases  :: [Int]
                               , compileInfoEvalCases   :: [Int]
                               , compileInfoNeedsBigInt :: Bool
                               }


initCompileInfo :: [(Name, [BC])] -> CompileInfo
initCompileInfo bc =
  CompileInfo (collectCases "APPLY" bc) (collectCases "EVAL" bc) (lookupBigInt bc)
  where
    lookupBigInt :: [(Name, [BC])] -> Bool
    lookupBigInt = any (needsBigInt . snd)
      where
        needsBigInt :: [BC] -> Bool
        needsBigInt bc = any testBCForBigInt bc
          where
            testBCForBigInt :: BC -> Bool
            testBCForBigInt (ASSIGNCONST _ c)  =
              testConstForBigInt c

            testBCForBigInt (CONSTCASE _ c d) =
                 maybe False needsBigInt d
              || any (needsBigInt . snd) c
              || any (testConstForBigInt . fst) c

            testBCForBigInt (CASE _ _ c d) =
                 maybe False needsBigInt d
              || any (needsBigInt . snd) c

            testBCForBigInt _ = False

            testConstForBigInt :: Const -> Bool
            testConstForBigInt (BI _)  = True
            testConstForBigInt (B64 _) = True
            testConstForBigInt _       = False


    collectCases :: String ->  [(Name, [BC])] -> [Int]
    collectCases fun bc = getCases $ findFunction fun bc

    findFunction :: String -> [(Name, [BC])] -> [BC]
    findFunction f ((MN 0 fun, bc):_)
      | fun == txt f = bc
    findFunction f (_:bc) = findFunction f bc

    getCases :: [BC] -> [Int]
    getCases = concatMap analyze
      where
        analyze :: BC -> [Int]
        analyze (CASE _ _ b _) = map fst b
        analyze _              = []


data JSTarget = Node | JavaScript deriving Eq


codegenJavaScript :: CodeGenerator
codegenJavaScript ci =
  codegenJS_all JavaScript (simpleDecls ci)
    (includes ci) [] (outputFile ci) (exportDecls ci) (outputType ci)

codegenNode :: CodeGenerator
codegenNode ci =
  codegenJS_all Node (simpleDecls ci)
    (includes ci) (compileLibs ci) (outputFile ci) (exportDecls ci) (outputType ci)

codegenJS_all
  :: JSTarget
  -> [(Name, SDecl)]
  -> [FilePath]
  -> [String]
  -> FilePath
  -> [ExportIFace]
  -> OutputType
  -> IO ()
codegenJS_all target definitions includes libs filename exports outputType = do
  let bytecode      = map toBC definitions
  let info          = initCompileInfo bytecode
  let js            = concatMap (translateDecl info) bytecode
  let full          = concatMap processFunction js
  let exportedNames = map translateName ((getExpNames exports) ++ [sUN "call__IO"])
  let code          = deadCodeElim exportedNames full
  let ext           = takeExtension filename
  let isHtml        = target == JavaScript && ext == ".html"
  let htmlPrologue  = T.pack "<!doctype html><html><head><script>\n"
  let htmlEpilogue  = T.pack "\n</script></head><body></body></html>"
  let (cons, opt)   = optimizeConstructors code
  let (header, rt)   = case target of
                          Node       -> ("#!/usr/bin/env node\n", "-node")
                          JavaScript -> ("", "-browser")

  included   <- concat <$> getIncludes includes
  path       <- getIdrisJSRTSDir
  idrRuntime <- readFile $ path </> "Runtime-common.js"
  tgtRuntime <- readFile $ path </> concat ["Runtime", rt, ".js"]
  jsbn       <- if compileInfoNeedsBigInt info
                   then readFile $ path </> "jsbn/jsbn.js"
                   else return ""
  let runtime = (  header
                ++ includeLibs libs
                ++ included
                ++ jsbn
                ++ idrRuntime
                ++ tgtRuntime
                )
  let jsSource = T.pack runtime
                 `T.append` T.concat (map compileJS opt)
                 `T.append` T.concat (map compileJS cons)
                 `T.append` T.concat (map compileJS (map genInterface (concatMap getExps exports)))
                 `T.append` main
                 `T.append` invokeMain
  let source = if isHtml
                    then htmlPrologue `T.append` jsSource `T.append` htmlEpilogue
                    else jsSource
  writeSourceText filename source
  setPermissions filename (emptyPermissions { readable   = True
                                            , executable = target == Node
                                            , writable   = True
                                            })
    where
      deadCodeElim :: [String] -> [JS] -> [JS]
      deadCodeElim exports js = concatMap (collectFunctions exports) js
        where
          collectFunctions :: [String] -> JS -> [JS]
          collectFunctions _ fun@(JSAlloc name _)
            | name == translateName (sMN 0 "runMain") = [fun]

          collectFunctions exports fun@(JSAlloc name _)
            | name `elem` exports = [fun]

          collectFunctions _ fun@(JSAlloc name (Just (JSFunction _ body))) =
            let invokations = sum $ map (
                    \x -> execState (countInvokations name x) 0
                  ) js
             in if invokations == 0
                   then []
                   else [fun]

          countInvokations :: String -> JS -> State Int ()
          countInvokations name (JSAlloc _ (Just (JSFunction _ body))) =
            countInvokations name body

          countInvokations name (JSSeq seq) =
            void $ traverse (countInvokations name) seq

          countInvokations name (JSAssign _ rhs) =
            countInvokations name rhs

          countInvokations name (JSCond conds) =
            void $ traverse (
                runKleisli $ arr id *** Kleisli (countInvokations name)
              ) conds

          countInvokations name (JSSwitch _ conds def) =
            void $ traverse (
              runKleisli $ arr id *** Kleisli (countInvokations name)
            ) conds >> traverse (countInvokations name) def

          countInvokations name (JSApp lhs rhs) =
            void $ countInvokations name lhs >> traverse (countInvokations name) rhs

          countInvokations name (JSNew _ args) =
            void $ traverse (countInvokations name) args

          countInvokations name (JSArray args) =
            void $ traverse (countInvokations name) args

          countInvokations name (JSIdent name')
            | name == name' = get >>= put . (+1)
            | otherwise     = return ()

          countInvokations _ _ = return ()

      processFunction :: JS -> [JS]
      processFunction =
        collectSplitFunctions . (\x -> evalRWS (splitFunction x) () 0)

      includeLibs :: [String] -> String
      includeLibs =
        concatMap (\lib -> "var " ++ lib ++ " = require(\"" ++ lib ++"\");\n")

      getIncludes :: [FilePath] -> IO [String]
      getIncludes = mapM readFile

      main :: T.Text
      main =
        compileJS $ JSAlloc "main" (Just $
          JSFunction [] (
            case target of
                 Node       -> mainFun
                 JavaScript -> jsMain
          )
        )

      jsMain :: JS
      jsMain =
        JSCond [ (exists document `jsAnd` isReady, mainFun)
               , (exists window, windowMainFun)
               , (JSTrue, mainFun)
               ]
        where
          exists :: JS -> JS
          exists js = jsTypeOf js `jsNotEq` JSString "undefined"

          window :: JS
          window = JSIdent "window"

          document :: JS
          document = JSIdent "document"

          windowMainFun :: JS
          windowMainFun =
            jsMeth window "addEventListener" [ JSString "DOMContentLoaded"
                                             , JSFunction [] ( mainFun )
                                             , JSFalse
                                             ]

          isReady :: JS
          isReady = JSParens $ readyState `jsEq` JSString "complete" `jsOr` readyState `jsEq` JSString "loaded"

          readyState :: JS
          readyState = JSProj (JSIdent "document") "readyState"

      mainFun :: JS
      mainFun =
        JSSeq [ JSAlloc "vm" (Just $ JSNew "i$VM" [])
              , JSApp (JSIdent "i$SCHED") [JSIdent "vm"]
              , JSApp (
                  JSIdent (translateName (sMN 0 "runMain"))
                ) [JSNew "i$POINTER" [JSNum (JSInt 0)]]
              , JSApp (JSIdent "i$RUN") []
              ]

      invokeMain :: T.Text
      invokeMain = compileJS $ JSApp (JSIdent "main") []
      getExps (Export _ _ exp) = exp

optimizeConstructors :: [JS] -> ([JS], [JS])
optimizeConstructors js =
    let (js', cons) = runState (traverse optimizeConstructor' js) M.empty in
        (map (allocCon . snd) (M.toList cons), js')
  where
    allocCon :: (String, JS) -> JS
    allocCon (name, con) = JSAlloc name (Just con)

    newConstructor :: Int -> String
    newConstructor n = "i$CON$" ++ show n

    optimizeConstructor' :: JS -> State (M.Map Int (String, JS)) JS
    optimizeConstructor' js@(JSNew "i$CON" [ JSNum (JSInt tag)
                                           , JSArray []
                                           , a
                                           , e
                                           ]) = do
      s <- get
      case M.lookup tag s of
           Just (i, c) -> return $ JSIdent i
           Nothing     -> do let n = newConstructor tag
                             put $ M.insert tag (n, js) s
                             return $ JSIdent n

    optimizeConstructor' (JSSeq seq) =
      JSSeq <$> traverse optimizeConstructor' seq

    optimizeConstructor' (JSSwitch reg cond def) = do
      cond' <- traverse (runKleisli $ arr id *** Kleisli optimizeConstructor') cond
      def'  <- traverse optimizeConstructor' def
      return $ JSSwitch reg cond' def'

    optimizeConstructor' (JSCond cond) =
      JSCond <$> traverse (runKleisli $ arr id *** Kleisli optimizeConstructor') cond

    optimizeConstructor' (JSAlloc fun (Just (JSFunction args body))) = do
      body' <- optimizeConstructor' body
      return $ JSAlloc fun (Just (JSFunction args body'))

    optimizeConstructor' (JSAssign lhs rhs) = do
      lhs' <- optimizeConstructor' lhs
      rhs' <- optimizeConstructor' rhs
      return $ JSAssign lhs' rhs'

    optimizeConstructor' js = return js

collectSplitFunctions :: (JS, [(Int,JS)]) -> [JS]
collectSplitFunctions (fun, splits) = map generateSplitFunction splits ++ [fun]
  where
    generateSplitFunction :: (Int,JS) -> JS
    generateSplitFunction (depth, JSAlloc name fun) =
      JSAlloc (name ++ "$" ++ show depth) fun

splitFunction :: JS -> RWS () [(Int,JS)] Int JS
splitFunction (JSAlloc name (Just (JSFunction args body@(JSSeq _)))) = do
  body' <- splitSequence body
  return $ JSAlloc name (Just (JSFunction args body'))
    where
      splitCondition :: JS -> RWS () [(Int,JS)] Int JS
      splitCondition js
        | JSCond branches <- js =
            JSCond <$> processBranches branches
        | JSSwitch cond branches def <- js =
            JSSwitch cond <$> (processBranches branches) <*> (traverse splitSequence def)
        | otherwise = return js
        where
          processBranches :: [(JS,JS)] -> RWS () [(Int,JS)] Int [(JS,JS)]
          processBranches =
            traverse (runKleisli (arr id *** Kleisli splitSequence))

      splitSequence :: JS -> RWS () [(Int, JS)] Int JS
      splitSequence js@(JSSeq seq) =
        let (pre,post) = break isBranch seq in
            case post of
                 [_] -> JSSeq <$> traverse splitCondition seq
                 [call@(JSCond _),rest@(JSApp _ _)]     -> do
                   rest' <- splitCondition rest
                   call' <- splitCondition call
                   return $ JSSeq (pre ++ [rest', call'])
                 [call@(JSSwitch _ _ _),rest@(JSApp _ _)] -> do
                   rest' <- splitCondition rest
                   call' <- splitCondition call
                   return $ JSSeq (pre ++ [rest', call'])
                 (call:rest) -> do
                   depth <- get
                   put (depth + 1)
                   new <- splitFunction (newFun rest)
                   tell [(depth, new)]
                   call' <- splitCondition call
                   return $ JSSeq (pre ++ (newCall depth : [call']))
                 _ -> JSSeq <$> traverse splitCondition seq

      splitSequence js = return js

      isBranch :: JS -> Bool
      isBranch (JSApp (JSIdent "i$CALL") _) = True
      isBranch (JSCond _)                   = True
      isBranch (JSSwitch _ _ _)             = True
      isBranch _                            = False

      newCall :: Int -> JS
      newCall depth =
        JSApp (JSIdent "i$CALL") [ JSIdent $ name ++ "$" ++ show depth
                                 , JSArray [jsOLDBASE, jsMYOLDBASE]
                                 ]

      newFun :: [JS] -> JS
      newFun seq =
        JSAlloc name (Just $ JSFunction ["oldbase", "myoldbase"] (JSSeq seq))

splitFunction js = return js

translateDecl :: CompileInfo -> (Name, [BC]) -> [JS]
translateDecl info (name@(MN 0 fun), bc)
  | txt "APPLY" == fun =
         allocCaseFunctions (snd body)
      ++ [ JSAlloc (
               translateName name
           ) (Just $ JSFunction ["oldbase"] (
               JSSeq $ jsFUNPRELUDE ++ map (translateBC info) (fst body) ++ [
                 JSCond [ ( (translateReg $ caseReg (snd body)) `jsInstanceOf` "i$CON" `jsAnd` (JSProj (translateReg $ caseReg (snd body)) "app")
                          , JSApp (JSProj (translateReg $ caseReg (snd body)) "app") [jsOLDBASE, jsMYOLDBASE]
                          )
                          , ( JSNoop
                            , JSSeq $ map (translateBC info) (defaultCase (snd body))
                            )
                        ]
               ]
             )
           )
         ]

  | txt "EVAL" == fun =
         allocCaseFunctions (snd body)
      ++ [ JSAlloc (
               translateName name
           ) (Just $ JSFunction ["oldbase"] (
               JSSeq $ jsFUNPRELUDE ++ map (translateBC info) (fst body) ++ [
                 JSCond [ ( (translateReg $ caseReg (snd body)) `jsInstanceOf` "i$CON" `jsAnd` (JSProj (translateReg $ caseReg (snd body)) "ev")
                          , JSApp (JSProj (translateReg $ caseReg (snd body)) "ev") [jsOLDBASE, jsMYOLDBASE]
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
      | CASE {} <- bc = True
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
      ) (Just $ JSFunction ["oldbase", "myoldbase"] (
          JSSeq $ map (translateBC info) code
        )
      )

translateDecl info (name, bc) =
  [ JSAlloc (
       translateName name
     ) (Just $ JSFunction ["oldbase"] (
         JSSeq $ jsFUNPRELUDE ++ map (translateBC info)bc
       )
     )
  ]

jsFUNPRELUDE :: [JS]
jsFUNPRELUDE = [jsALLOCMYOLDBASE]

jsALLOCMYOLDBASE :: JS
jsALLOCMYOLDBASE = JSAlloc "myoldbase" (Just $ JSNew "i$POINTER" [])

translateReg :: Reg -> JS
translateReg reg
  | RVal <- reg = jsRET
  | Tmp  <- reg = JSRaw "//TMPREG"
  | L n  <- reg = jsLOC n
  | T n  <- reg = jsTOP n

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
translateConstant Forgot                   = JSType JSForgotTy
translateConstant (BI 0)                   = JSNum (JSInteger JSBigZero)
translateConstant (BI 1)                   = JSNum (JSInteger JSBigOne)
translateConstant (BI i)                   = jsBigInt (JSString $ show i)
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
  | ch `elem` asciiTab = "\\u" ++ fill (showHex (ord ch) "")
  | ord ch > 255       = "\\u" ++ fill (showHex (ord ch) "")
  | otherwise          = [ch]
  where
    fill :: String -> String
    fill s = case length s of
                  1 -> "000" ++ s
                  2 -> "00"  ++ s
                  3 -> "0"   ++ s
                  _ ->          s

    asciiTab =
      ['\NUL', '\SOH', '\STX', '\ETX', '\EOT', '\ENQ', '\ACK', '\BEL',
       '\BS',  '\HT',  '\LF',  '\VT',  '\FF',  '\CR',  '\SO',  '\SI',
       '\DLE', '\DC1', '\DC2', '\DC3', '\DC4', '\NAK', '\SYN', '\ETB',
       '\CAN', '\EM',  '\SUB', '\ESC', '\FS',  '\GS',  '\RS',  '\US']

translateName :: Name -> String
translateName n = "_idris_" ++ concatMap cchar (showCG n)
  where cchar x | isAlphaNum x = [x]
                | otherwise    = "_" ++ show (fromEnum x) ++ "_"

jsASSIGN :: CompileInfo -> Reg -> Reg -> JS
jsASSIGN _ r1 r2 = JSAssign (translateReg r1) (translateReg r2)

jsASSIGNCONST :: CompileInfo -> Reg -> Const -> JS
jsASSIGNCONST _ r c = JSAssign (translateReg r) (translateConstant c)

jsCALL :: CompileInfo -> Name -> JS
jsCALL _ n =
  JSApp (
    JSIdent "i$CALL"
  ) [JSIdent (translateName n), JSArray [jsMYOLDBASE]]

jsTAILCALL :: CompileInfo -> Name -> JS
jsTAILCALL _ n =
  JSApp (
    JSIdent "i$CALL"
  ) [JSIdent (translateName n), JSArray [jsOLDBASE]]

jsFOREIGN :: CompileInfo -> Reg -> String -> [(FType, Reg)] -> JS
jsFOREIGN _ reg n args
  | n == "isNull"
  , [(FPtr, arg)] <- args =
      JSAssign (
        translateReg reg
      ) (
        JSBinOp "==" (translateReg arg) JSNull
      )

  | n == "idris_eqPtr"
  , [(_, lhs),(_, rhs)] <- args =
      JSAssign (
        translateReg reg
      ) (
        JSBinOp "==" (translateReg lhs) (translateReg rhs)
      )
  | otherwise =
     JSAssign (
       translateReg reg
     ) (
       JSFFI n (map generateWrapper args)
     )
    where
      generateWrapper :: (FType, Reg) -> JS
      generateWrapper (ty, reg)
        | FFunction   <- ty =
            JSApp (JSIdent "i$ffiWrap") [ translateReg reg
                                        , JSIdent "oldbase"
                                        , JSIdent "myoldbase"
                                        ]
        | FFunctionIO <- ty =
            JSApp (JSIdent "i$ffiWrap") [ translateReg reg
                                        , JSIdent "oldbase"
                                        , JSIdent "myoldbase"
                                        ]

      generateWrapper (_, reg) =
        translateReg reg

jsREBASE :: CompileInfo -> JS
jsREBASE _ = JSAssign jsSTACKBASE (JSProj jsOLDBASE "addr")

jsSTOREOLD :: CompileInfo ->JS
jsSTOREOLD _ = JSAssign (JSProj jsMYOLDBASE "addr") jsSTACKBASE

jsADDTOP :: CompileInfo -> Int -> JS
jsADDTOP info n
  | 0 <- n    = JSNoop
  | otherwise =
      JSBinOp "+=" jsSTACKTOP (JSNum (JSInt n))

jsTOPBASE :: CompileInfo -> Int -> JS
jsTOPBASE _ 0  = JSAssign jsSTACKTOP jsSTACKBASE
jsTOPBASE _ n  = JSAssign jsSTACKTOP (JSBinOp "+" jsSTACKBASE (JSNum (JSInt n)))


jsBASETOP :: CompileInfo -> Int -> JS
jsBASETOP _ 0 = JSAssign jsSTACKBASE jsSTACKTOP
jsBASETOP _ n = JSAssign jsSTACKBASE (JSBinOp "+" jsSTACKTOP (JSNum (JSInt n)))

jsNULL :: CompileInfo -> Reg -> JS
jsNULL _ r = JSClear (translateReg r)

jsERROR :: CompileInfo -> String -> JS
jsERROR _ = JSError

jsSLIDE :: CompileInfo -> Int -> JS
jsSLIDE _ 1 = JSAssign (jsLOC 0) (jsTOP 0)
jsSLIDE _ n = JSApp (JSIdent "i$SLIDE") [JSNum (JSInt n)]

jsMKCON :: CompileInfo -> Reg -> Int -> [Reg] -> JS
jsMKCON info r t rs =
  JSAssign (translateReg r) (
    JSNew "i$CON" [ JSNum (JSInt t)
                  , JSArray (map translateReg rs)
                  , if t `elem` compileInfoApplyCases info
                       then JSIdent $ translateName (sMN 0 "APPLY") ++ "$" ++ show t
                       else JSNull
                  , if t `elem` compileInfoEvalCases info
                       then JSIdent $ translateName (sMN 0 "EVAL") ++ "$" ++ show t
                       else JSNull
                  ]
  )

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
        (JSTernary (js `jsInstanceOf` "i$CON") (
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
jsPROJECT _ reg loc 0  = JSNoop
jsPROJECT _ reg loc 1  =
  JSAssign (jsLOC loc) (
    JSIndex (
      JSProj (translateReg reg) "args"
    ) (
      JSNum (JSInt 0)
    )
  )
jsPROJECT _ reg loc ar =
  JSApp (JSIdent "i$PROJECT") [ translateReg reg
                              , JSNum (JSInt loc)
                              , JSNum (JSInt ar)
                              ]

jsOP :: CompileInfo -> Reg -> PrimFn -> [Reg] -> JS
jsOP _ reg op args = JSAssign (translateReg reg) jsOP'
  where
    jsOP' :: JS
    jsOP'
      | LNoOp <- op = translateReg (last args)

      | LWriteStr <- op,
        (_:str:_) <- args = JSApp (JSIdent "i$putStr") [translateReg str]

      | LReadStr <- op  = JSApp (JSIdent "i$getLine") []

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
      , (lhs:rhs:_)            <- args = JSPreOp "+" $ invokeMeth lhs "equals" [rhs]
      | (LSLt (ATInt ITBig))   <- op
      , (lhs:rhs:_)            <- args = JSPreOp "+" $ invokeMeth lhs "lesser" [rhs]
      | (LSLe (ATInt ITBig))   <- op
      , (lhs:rhs:_)            <- args = JSPreOp "+" $ invokeMeth lhs "lesserOrEquals" [rhs]
      | (LSGt (ATInt ITBig))   <- op
      , (lhs:rhs:_)            <- args = JSPreOp "+" $ invokeMeth lhs "greater" [rhs]
      | (LSGe (ATInt ITBig))   <- op
      , (lhs:rhs:_)            <- args = JSPreOp "+" $ invokeMeth lhs "greaterOrEquals" [rhs]

      | (LPlus ATFloat)  <- op
      , (lhs:rhs:_)      <- args = translateBinaryOp "+" lhs rhs
      | (LMinus ATFloat) <- op
      , (lhs:rhs:_)      <- args = translateBinaryOp "-" lhs rhs
      | (LTimes ATFloat) <- op
      , (lhs:rhs:_)      <- args = translateBinaryOp "*" lhs rhs
      | (LSDiv ATFloat)  <- op
      , (lhs:rhs:_)      <- args = translateBinaryOp "/" lhs rhs
      | (LEq ATFloat)    <- op
      , (lhs:rhs:_)      <- args = translateCompareOp "==" lhs rhs
      | (LSLt ATFloat)   <- op
      , (lhs:rhs:_)      <- args = translateCompareOp "<" lhs rhs
      | (LSLe ATFloat)   <- op
      , (lhs:rhs:_)      <- args = translateCompareOp "<=" lhs rhs
      | (LSGt ATFloat)   <- op
      , (lhs:rhs:_)      <- args = translateCompareOp ">" lhs rhs
      | (LSGe ATFloat)   <- op
      , (lhs:rhs:_)      <- args = translateCompareOp ">=" lhs rhs

      | (LPlus (ATInt ITChar)) <- op
      , (lhs:rhs:_)            <- args =
          jsCall "i$fromCharCode" [
            JSBinOp "+" (
              jsCall "i$charCode" [translateReg lhs]
            ) (
              jsCall "i$charCode" [translateReg rhs]
            )
          ]

      | (LTrunc (ITFixed _from) (ITFixed IT8)) <- op
      , (arg:_)                               <- args =
          jsPackUBits8 (
            JSBinOp "&" (jsUnPackBits $ translateReg arg) (JSNum (JSInt 0xFF))
          )

      | (LTrunc (ITFixed _from) (ITFixed IT16)) <- op
      , (arg:_)                                <- args =
          jsPackUBits16 (
            JSBinOp "&" (jsUnPackBits $ translateReg arg) (JSNum (JSInt 0xFFFF))
          )

      | (LTrunc (ITFixed _from) (ITFixed IT32)) <- op
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
      , (lhs:rhs:_)           <- args = jsPackUBits8 $ bitsBinaryOp ">>" lhs rhs

      | (LLSHR (ITFixed IT16)) <- op
      , (lhs:rhs:_)            <- args = jsPackUBits16 $ bitsBinaryOp ">>" lhs rhs

      | (LLSHR (ITFixed IT32)) <- op
      , (lhs:rhs:_)            <- args = jsPackUBits32 $ bitsBinaryOp ">>" lhs rhs

      | (LLSHR (ITFixed IT64)) <- op
      , (lhs:rhs:_)            <- args =
          jsMeth (translateReg lhs) "shiftRight" [translateReg rhs]

      | (LSHL (ITFixed IT8)) <- op
      , (lhs:rhs:_)          <- args = jsPackUBits8 $ bitsBinaryOp "<<" lhs rhs

      | (LSHL (ITFixed IT16)) <- op
      , (lhs:rhs:_)           <- args = jsPackUBits16 $ bitsBinaryOp "<<" lhs rhs

      | (LSHL (ITFixed IT32)) <- op
      , (lhs:rhs:_)           <- args = jsPackUBits32 $ bitsBinaryOp "<<" lhs rhs

      | (LSHL (ITFixed IT64)) <- op
      , (lhs:rhs:_)           <- args =
          jsMeth (jsMeth (translateReg lhs) "shiftLeft" [translateReg rhs]) "and" [
            jsBigInt (JSString $ show 0xFFFFFFFFFFFFFFFF)
          ]

      | (LAnd (ITFixed IT8)) <- op
      , (lhs:rhs:_)          <- args = jsPackUBits8 $ bitsBinaryOp "&" lhs rhs

      | (LAnd (ITFixed IT16)) <- op
      , (lhs:rhs:_)           <- args = jsPackUBits16 $ bitsBinaryOp "&" lhs rhs

      | (LAnd (ITFixed IT32)) <- op
      , (lhs:rhs:_)           <- args = jsPackUBits32 $ bitsBinaryOp "&" lhs rhs

      | (LAnd (ITFixed IT64)) <- op
      , (lhs:rhs:_)           <- args =
          jsMeth (translateReg lhs) "and" [translateReg rhs]

      | (LOr (ITFixed IT8)) <- op
      , (lhs:rhs:_)         <- args = jsPackUBits8 $ bitsBinaryOp "|" lhs rhs

      | (LOr (ITFixed IT16)) <- op
      , (lhs:rhs:_)          <- args = jsPackUBits16 $ bitsBinaryOp "|" lhs rhs

      | (LOr (ITFixed IT32)) <- op
      , (lhs:rhs:_)          <- args = jsPackUBits32 $ bitsBinaryOp "|" lhs rhs

      | (LOr (ITFixed IT64)) <- op
      , (lhs:rhs:_)          <- args =
          jsMeth (translateReg lhs) "or" [translateReg rhs]

      | (LXOr (ITFixed IT8)) <- op
      , (lhs:rhs:_)          <- args = jsPackUBits8 $ bitsBinaryOp "^" lhs rhs

      | (LXOr (ITFixed IT16)) <- op
      , (lhs:rhs:_)           <- args = jsPackUBits16 $ bitsBinaryOp "^" lhs rhs

      | (LXOr (ITFixed IT32)) <- op
      , (lhs:rhs:_)           <- args = jsPackUBits32 $ bitsBinaryOp "^" lhs rhs

      | (LXOr (ITFixed IT64)) <- op
      , (lhs:rhs:_)           <- args =
          jsMeth (translateReg lhs) "xor" [translateReg rhs]

      | (LPlus (ATInt (ITFixed IT8))) <- op
      , (lhs:rhs:_)                   <- args = jsPackUBits8 $ bitsBinaryOp "+" lhs rhs

      | (LPlus (ATInt (ITFixed IT16))) <- op
      , (lhs:rhs:_)                    <- args = jsPackUBits16 $ bitsBinaryOp "+" lhs rhs

      | (LPlus (ATInt (ITFixed IT32))) <- op
      , (lhs:rhs:_)                    <- args = jsPackUBits32 $ bitsBinaryOp "+" lhs rhs

      | (LPlus (ATInt (ITFixed IT64))) <- op
      , (lhs:rhs:_)                    <- args =
          jsMeth (jsMeth (translateReg lhs) "add" [translateReg rhs]) "and" [
            jsBigInt (JSString $ show 0xFFFFFFFFFFFFFFFF)
          ]

      | (LMinus (ATInt (ITFixed IT8))) <- op
      , (lhs:rhs:_)                    <- args = jsPackUBits8 $ bitsBinaryOp "-" lhs rhs

      | (LMinus (ATInt (ITFixed IT16))) <- op
      , (lhs:rhs:_)                     <- args = jsPackUBits16 $ bitsBinaryOp "-" lhs rhs

      | (LMinus (ATInt (ITFixed IT32))) <- op
      , (lhs:rhs:_)                     <- args = jsPackUBits32 $ bitsBinaryOp "-" lhs rhs

      | (LMinus (ATInt (ITFixed IT64))) <- op
      , (lhs:rhs:_)                     <- args =
          jsMeth (jsMeth (translateReg lhs) "subtract" [translateReg rhs]) "and" [
            jsBigInt (JSString $ show 0xFFFFFFFFFFFFFFFF)
          ]

      | (LTimes (ATInt (ITFixed IT8))) <- op
      , (lhs:rhs:_)                    <- args = jsPackUBits8 $ bitsBinaryOp "*" lhs rhs

      | (LTimes (ATInt (ITFixed IT16))) <- op
      , (lhs:rhs:_)                     <- args = jsPackUBits16 $ bitsBinaryOp "*" lhs rhs

      | (LTimes (ATInt (ITFixed IT32))) <- op
      , (lhs:rhs:_)                     <- args = jsPackUBits32 $ bitsBinaryOp "*" lhs rhs

      | (LTimes (ATInt (ITFixed IT64))) <- op
      , (lhs:rhs:_)                     <- args =
          jsMeth (jsMeth (translateReg lhs) "multiply" [translateReg rhs]) "and" [
            jsBigInt (JSString $ show 0xFFFFFFFFFFFFFFFF)
          ]

      | (LEq (ATInt (ITFixed IT8))) <- op
      , (lhs:rhs:_)                 <- args = bitsCompareOp "==" lhs rhs

      | (LEq (ATInt (ITFixed IT16))) <- op
      , (lhs:rhs:_)                  <- args = bitsCompareOp "==" lhs rhs

      | (LEq (ATInt (ITFixed IT32))) <- op
      , (lhs:rhs:_)                  <- args = bitsCompareOp "==" lhs rhs

      | (LEq (ATInt (ITFixed IT64))) <- op
      , (lhs:rhs:_)                  <- args = JSPreOp "+" $ invokeMeth lhs "equals" [rhs]

      | (LLt (ITFixed IT8)) <- op
      , (lhs:rhs:_)         <- args = bitsCompareOp "<" lhs rhs

      | (LLt (ITFixed IT16)) <- op
      , (lhs:rhs:_)          <- args = bitsCompareOp "<" lhs rhs

      | (LLt (ITFixed IT32)) <- op
      , (lhs:rhs:_)          <- args = bitsCompareOp "<" lhs rhs

      | (LLt (ITFixed IT64)) <- op
      , (lhs:rhs:_)          <- args = JSPreOp "+" $ invokeMeth lhs "lesser" [rhs]

      | (LLe (ITFixed IT8)) <- op
      , (lhs:rhs:_)         <- args = bitsCompareOp "<=" lhs rhs

      | (LLe (ITFixed IT16)) <- op
      , (lhs:rhs:_)          <- args = bitsCompareOp "<=" lhs rhs

      | (LLe (ITFixed IT32)) <- op
      , (lhs:rhs:_)          <- args = bitsCompareOp "<=" lhs rhs

      | (LLe (ITFixed IT64)) <- op
      , (lhs:rhs:_)          <- args = JSPreOp "+" $ invokeMeth lhs "lesserOrEquals" [rhs]

      | (LGt (ITFixed IT8)) <- op
      , (lhs:rhs:_)         <- args = bitsCompareOp ">" lhs rhs

      | (LGt (ITFixed IT16)) <- op
      , (lhs:rhs:_)          <- args = bitsCompareOp ">" lhs rhs
      | (LGt (ITFixed IT32)) <- op
      , (lhs:rhs:_)          <- args = bitsCompareOp ">" lhs rhs

      | (LGt (ITFixed IT64)) <- op
      , (lhs:rhs:_)          <- args = JSPreOp "+" $ invokeMeth lhs "greater" [rhs]

      | (LGe (ITFixed IT8)) <- op
      , (lhs:rhs:_)         <- args = bitsCompareOp ">=" lhs rhs

      | (LGe (ITFixed IT16)) <- op
      , (lhs:rhs:_)          <- args = bitsCompareOp ">=" lhs rhs
      | (LGe (ITFixed IT32)) <- op
      , (lhs:rhs:_)          <- args = bitsCompareOp ">=" lhs rhs

      | (LGe (ITFixed IT64)) <- op
      , (lhs:rhs:_)          <- args = JSPreOp "+" $ invokeMeth lhs "greaterOrEquals" [rhs]

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
      , (arg:_)                 <- args = invokeMeth arg "not" []

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
      , (lhs:rhs:_) <- args = translateCompareOp "==" lhs rhs
      | (LSLt _)    <- op
      , (lhs:rhs:_) <- args = translateCompareOp "<" lhs rhs
      | (LSLe _)    <- op
      , (lhs:rhs:_) <- args = translateCompareOp "<=" lhs rhs
      | (LSGt _)    <- op
      , (lhs:rhs:_) <- args = translateCompareOp ">" lhs rhs
      | (LSGe _)    <- op
      , (lhs:rhs:_) <- args = translateCompareOp ">=" lhs rhs
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
      , (lhs:rhs:_) <- args = translateCompareOp "==" lhs rhs
      | LStrLt      <- op
      , (lhs:rhs:_) <- args = translateCompareOp "<" lhs rhs
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
      | (LIntFloat ITBig)       <- op
      , (arg:_)                 <- args = jsMeth (translateReg arg) "intValue" []
      | (LFloatInt ITNative)    <- op
      , (arg:_)                 <- args = translateReg arg
      | (LChInt ITNative)       <- op
      , (arg:_)                 <- args = jsCall "i$charCode" [translateReg arg]
      | (LIntCh ITNative)       <- op
      , (arg:_)                 <- args = jsCall "i$fromCharCode" [translateReg arg]

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
      | LFNegate    <- op
      , (arg:_)     <- args = JSPreOp "-" (translateReg arg)

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
      | LStrSubstr <- op
      , (offset:length:string:_) <- args =
        let off = translateReg offset
            len = translateReg length
            str = translateReg string
        in JSApp (JSProj str "substr") [
             jsCall "Math.max" [JSNum (JSInt 0), off],
             jsCall "Math.max" [JSNum (JSInt 0), len]
           ]

      | LSystemInfo <- op
      , (arg:_) <- args = jsCall "i$systemInfo"  [translateReg arg]
      | LExternal nul <- op
      , nul == sUN "prim__null"
      , _ <- args = JSNull
      | LExternal ex <- op
      , ex == sUN "prim__eqPtr"
      , [lhs, rhs] <- args = translateCompareOp "==" lhs rhs
      | otherwise = JSError $ "Not implemented: " ++ show op
        where
          translateBinaryOp :: String -> Reg -> Reg -> JS
          translateBinaryOp op lhs rhs =
            JSBinOp op (translateReg lhs) (translateReg rhs)

          translateCompareOp :: String -> Reg -> Reg -> JS
          translateCompareOp op lhs rhs =
            JSPreOp "+" $ translateBinaryOp op lhs rhs

          bitsBinaryOp :: String -> Reg -> Reg -> JS
          bitsBinaryOp op lhs rhs =
            JSBinOp op (jsUnPackBits (translateReg lhs)) (jsUnPackBits (translateReg rhs))

          bitsCompareOp :: String -> Reg -> Reg -> JS
          bitsCompareOp op lhs rhs =
            JSPreOp "+" $ bitsBinaryOp op lhs rhs

          invokeMeth :: Reg -> String -> [Reg] -> JS
          invokeMeth obj meth args =
            JSApp (JSProj (translateReg obj) meth) $ map translateReg args


jsRESERVE :: CompileInfo -> Int -> JS
jsRESERVE _ _ = JSNoop

jsSTACK :: JS
jsSTACK = JSIdent "i$valstack"

jsCALLSTACK :: JS
jsCALLSTACK = JSIdent "i$callstack"

jsSTACKBASE :: JS
jsSTACKBASE = JSIdent "i$valstack_base"

jsSTACKTOP :: JS
jsSTACKTOP = JSIdent "i$valstack_top"

jsOLDBASE :: JS
jsOLDBASE = JSIdent "oldbase"

jsMYOLDBASE :: JS
jsMYOLDBASE = JSIdent "myoldbase"

jsRET :: JS
jsRET = JSIdent "i$ret"

jsLOC :: Int -> JS
jsLOC 0 = JSIndex jsSTACK jsSTACKBASE
jsLOC n = JSIndex jsSTACK (JSBinOp "+" jsSTACKBASE (JSNum (JSInt n)))

jsTOP :: Int -> JS
jsTOP 0 = JSIndex jsSTACK jsSTACKTOP
jsTOP n = JSIndex jsSTACK (JSBinOp "+" jsSTACKTOP (JSNum (JSInt n)))

jsPUSH :: [JS] -> JS
jsPUSH args = JSApp (JSProj jsCALLSTACK "push") args

jsPOP :: JS
jsPOP = JSApp (JSProj jsCALLSTACK "pop") []

genInterface :: Export -> JS
genInterface (ExportData name) = JSNoop
genInterface (ExportFun name (FStr jsName) ret args) = JSAlloc jsName
        (Just (JSFunction [] (JSSeq  $
            jsFUNPRELUDE ++
            pushArgs nargs ++
            [jsSTOREOLD d,
             jsBASETOP d 0,
             jsADDTOP d nargs,
             jsCALL d name] ++
            retval ret)))
    where
        nargs = length args
        d = CompileInfo [] [] False
        pushArg n = JSAssign (jsTOP n) (JSIndex (JSIdent "arguments") (JSNum (JSInt n)))
        pushArgs 0 = []
        pushArgs n = (pushArg (n-1)):pushArgs (n-1)
        retval (FIO t) = [JSApp (JSIdent "i$RUN") [],
                          JSAssign (jsTOP 0) JSNull,
                          JSAssign (jsTOP 1) JSNull,
                          JSAssign (jsTOP 2) (translateReg RVal),
                          jsSTOREOLD d,
                          jsBASETOP d 0,
                          jsADDTOP d 3,
                          jsCALL d (sUN "call__IO")] ++ retval t
        retval t = [JSApp (JSIdent "i$RUN") [], JSReturn (translateReg RVal)]

translateBC :: CompileInfo -> BC -> JS
translateBC info bc
  | ASSIGN r1 r2          <- bc = jsASSIGN info r1 r2
  | ASSIGNCONST r c       <- bc = jsASSIGNCONST info r c
  | UPDATE r1 r2          <- bc = jsASSIGN info r1 r2
  | ADDTOP n              <- bc = jsADDTOP info n
  | NULL r                <- bc = jsNULL info r
  | CALL n                <- bc = jsCALL info n
  | TAILCALL n            <- bc = jsTAILCALL info n
  | FOREIGNCALL r _ (FStr n) args
                          <- bc = jsFOREIGN info r n (map fcall args)
  | FOREIGNCALL _ _ _ _   <- bc = error "JS FFI call not statically known"
  | TOPBASE n             <- bc = jsTOPBASE info n
  | BASETOP n             <- bc = jsBASETOP info n
  | STOREOLD              <- bc = jsSTOREOLD info
  | SLIDE n               <- bc = jsSLIDE info n
  | REBASE                <- bc = jsREBASE info
  | RESERVE n             <- bc = jsRESERVE info n
  | MKCON r _ t rs        <- bc = jsMKCON info r t rs
  | CASE s r c d          <- bc = jsCASE info s r c d
  | CONSTCASE r c d       <- bc = jsCONSTCASE info r c d
  | PROJECT r l a         <- bc = jsPROJECT info r l a
  | OP r o a              <- bc = jsOP info r o a
  | ERROR e               <- bc = jsERROR info e
  | otherwise                   = JSRaw $ "//" ++ show bc
 where fcall (t, arg) = (toFType t, arg)

toAType (FCon i)
    | i == sUN "JS_IntChar" = ATInt ITChar
    | i == sUN "JS_IntNative" = ATInt ITNative
toAType t = error (show t ++ " not defined in toAType")

toFnType (FApp c [_,_,s,t])
    | c == sUN "JS_Fn" = toFnType t
toFnType (FApp c [_,_,r])
    | c == sUN "JS_FnIO" = FFunctionIO
toFnType (FApp c [_,r])
    | c == sUN "JS_FnBase" = FFunction
toFnType t = error (show t ++ " not defined in toFnType")

toFType (FCon c)
    | c == sUN "JS_Str" = FString
    | c == sUN "JS_Float" = FArith ATFloat
    | c == sUN "JS_Ptr" = FPtr
    | c == sUN "JS_Unit" = FUnit
toFType (FApp c [_,ity])
    | c == sUN "JS_IntT" = FArith (toAType ity)
toFType (FApp c [_,fty])
    | c == sUN "JS_FnT" = toFnType fty
toFType t = error (show t ++ " not yet defined in toFType")
