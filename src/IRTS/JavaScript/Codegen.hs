{-|
Module      : IRTS.JavaScript.Codegen
Description : The JavaScript common code generator.
Copyright   :
License     : BSD3
Maintainer  : The Idris Community.
-}
{-# LANGUAGE OverloadedStrings #-}

module IRTS.JavaScript.Codegen( codegenJs
                              , CGConf(..)
                              , CGStats(..)
                              ) where

import Control.DeepSeq
import IRTS.CodegenCommon
import IRTS.Lang
import Idris.Core.TT
import IRTS.LangOpts
import IRTS.JavaScript.AST
import IRTS.JavaScript.LangTransforms
import IRTS.System

import Data.Maybe (fromJust)
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.List (nub)
import System.Directory (doesFileExist)
import System.FilePath
import Control.Monad.Trans.State
import System.Environment

import GHC.Generics (Generic)
import Data.Data
import Data.Generics.Uniplate.Data
import Data.List
import Data.Char

data Partial = Partial Name Int Int deriving (Eq, Ord)

data CGStats = CGStats { usedWriteStr :: Bool
                       , usedReadStr :: Bool
                       , usedBigInt :: Bool
                       , partialApplications :: Set Partial
                       }

emptyStats :: CGStats
emptyStats = CGStats {usedWriteStr = False, partialApplications = Set.empty, usedBigInt = False, usedReadStr = False}

data CGConf = CGConf { header :: Text
                     , footer :: Text
                     , initialization :: CGStats -> Text
                     , writeStrTemplate :: Text
                     , readStrTemplate :: Text
                     }


get_include :: FilePath -> IO Text
get_include p = TIO.readFile p

get_includes :: [FilePath] -> IO Text
get_includes l = do
  incs <- mapM get_include l
  return $ T.intercalate "\n\n" incs

isYes :: Maybe String -> Bool
isYes (Just "Y") = True
isYes (Just "y") = True
isYes _ = False


codegenJs :: CGConf -> CodeGenerator
codegenJs conf ci =
  do
    optim <- isYes <$> lookupEnv "IDRISJS_OPTIM"
    debug <- isYes <$> lookupEnv "IDRISJS_DEBUG"
    if debug then
      if optim then putStrLn "compiling width idris-js optimizations"
        else putStrLn "compiling widthout idris-js optimizations"
      else pure ()
    let defs = Map.fromList $ liftDecls ci
    let used = Map.elems $ used_defs defs [sMN 0 "runMain"]
    used `deepseq` if debug then
      do
        putStrLn $ "Finished calculating used"
        writeFile (outputFile ci ++ ".LDeclsDebug") $ (unlines $ intersperse "" $ map show used) ++ "\n\n\n"
      else pure ()

    let (out, stats) = doCodegen conf defs used

    path <- getIdrisJSRTSDir
    jsbn <- if usedBigInt stats
              then TIO.readFile $ path </> "jsbn/jsbn.js"
              else return ""


    out `deepseq` if debug then putStrLn $ "Finished generating code" else pure ()
    includes <- get_includes $ includes ci
    TIO.writeFile (outputFile ci) $ T.concat [ header conf
                                             , "\"use strict\";\n\n"
                                             , "(function(){\n\n"
                                             , jsbn
                                             , initialization conf stats
                                             , doPartials (partialApplications stats)
                                             , includes, "\n"
                                             , js_aux_defs, "\n"
                                             , out, "\n"
                                             , "\n"
                                             , jsName (sMN 0 "runMain"), "();\n\n"
                                             , "\n}.call(this))"
                                             , footer conf
                                             ]

jsName :: Name -> Text
jsName n = T.pack $ "idris_" ++ concatMap jschar (showCG n)
  where jschar x | isAlpha x || isDigit x = [x]
                  | otherwise = "_" ++ show (fromEnum x) ++ "_"

jsPartialName :: Partial -> Text
jsPartialName (Partial n i j) = T.concat ["partial_", T.pack $ show i, "_", T.pack $ show j, "_" , jsName n]

jsTailCallOptimName :: Text -> Text
jsTailCallOptimName x = T.concat ["tailCallOptim_cgIdris_", x]

doPartials :: Set Partial -> Text
doPartials x =
  T.intercalate "\n" (map f $ Set.toList x)
  where
      f p@(Partial n i j) =
        let vars1 = map (T.pack . ("x"++) . show) [1..i]
            vars2 = map (T.pack . ("x"++) . show) [(i+1)..j]
        in jsAst2Text $
             JsFun (jsPartialName p) vars1 $ JsReturn $ JsCurryLambda vars2 (JsApp (jsName n) (map JsVar (vars1 ++ vars2)) )

doCodegen :: CGConf -> Map Name LDecl -> [LDecl] -> (Text, CGStats)
doCodegen conf defs decls =
  let xs = map (doCodegenDecl conf defs) decls
      groupCGStats x y = CGStats {usedWriteStr = usedWriteStr x || usedWriteStr y
                                 , partialApplications = partialApplications x `Set.union` partialApplications y
                                 , usedBigInt = usedBigInt x || usedBigInt y
                                 , usedReadStr = usedReadStr x || usedReadStr y
                                 }
  in (T.intercalate "\n" $ map fst xs, foldl' groupCGStats emptyStats (map snd xs) )

doCodegenDecl :: CGConf -> Map Name LDecl -> LDecl -> (Text, CGStats)
doCodegenDecl conf defs (LFun _ n args def) =
  let (ast, stats) = cgFun conf defs n args def
  in (jsAst2Text $ ast, stats)
doCodegenDecl conf defs (LConstructor n i sz) =
  ("", emptyStats)

seqJs :: [JsAST] -> JsAST
seqJs [] = JsEmpty
seqJs (x:xs) = JsSeq x (seqJs xs)


data CGBodyState = CGBodyState { defs :: Map Name LDecl
                               , lastIntName :: Int
                               , currentFnNameAndArgs :: (Text, [Text])
                               , usedArgsTailCallOptim :: Set (Text, Text)
                               , isTailRec :: Bool
                               , conf :: CGConf
                               , usedWrite :: Bool
                               , usedRead :: Bool
                               , usedITBig :: Bool
                               , partialApps :: Set Partial
                               }

getNewCGName :: State CGBodyState Text
getNewCGName =
  do
    st <- get
    let v = lastIntName st + 1
    put $ st {lastIntName = v}
    return $ T.pack $ "cgIdris_" ++ show v

addPartial :: Partial -> State CGBodyState ()
addPartial p =
  modify (\s -> s {partialApps = Set.insert p (partialApps s) })

addUsedArgsTailCallOptim :: Set (Text, Text) -> State CGBodyState ()
addUsedArgsTailCallOptim p =
  modify (\s -> s {usedArgsTailCallOptim = Set.union p (usedArgsTailCallOptim s) })

getNewCGNames :: Int -> State CGBodyState [Text]
getNewCGNames n =
  mapM (\_ -> getNewCGName) [1..n]

getConsId :: Name -> State CGBodyState Int
getConsId n =
    do
      st <- get
      case Map.lookup n (defs st) of
        Just (LConstructor _ conId _) -> pure conId
        _ -> error $ "Internal JS Backend error " ++ showCG n ++ " is not a constructor."

getArgList :: Name -> State CGBodyState (Maybe [Name])
getArgList n =
  do
    st <- get
    case Map.lookup n (defs st) of
      Just (LFun _ _ a _) -> pure $ Just a
      _ -> pure Nothing

data BodyResTarget = ReturnBT
                   | DecBT Text
                   | SetBT Text
                   | DecConstBT Text
                   | GetExpBT

replaceVarsByProj :: JsAST -> Map Text Int -> JsAST -> JsAST
replaceVarsByProj n d z =
  transform f z
  where
    f :: JsAST -> JsAST
    f (JsVar x) =
      case Map.lookup x d of
        Nothing -> (JsVar x)
        Just i -> JsArrayProj (JsInt i) n
    f x = x

cgFun :: CGConf -> Map Name LDecl -> Name -> [Name] -> LExp -> (JsAST, CGStats)
cgFun cnf dfs n args def =
  let
      fnName = jsName n
      argNames = map jsName args
      ((decs, res),st) = runState
                          (cgBody ReturnBT def)
                          (CGBodyState { defs=dfs
                                       , lastIntName = 0
                                       , currentFnNameAndArgs = (fnName, argNames)
                                       , usedArgsTailCallOptim = Set.empty
                                       , isTailRec = False
                                       , conf = cnf
                                       , usedWrite = False
                                       , usedRead = False
                                       , usedITBig = False
                                       , partialApps = Set.empty
                                       }
                          )
      body = if isTailRec st then
                JsSeq
                 (declareUsedOptimArgs $ usedArgsTailCallOptim st)
                 (JsWhileTrue ((seqJs decs) `JsSeq` res))
                else (seqJs decs) `JsSeq` res
  in (JsFun fnName argNames $ body, CGStats { usedWriteStr = usedWrite st
                                            , partialApplications = partialApps st
                                            , usedBigInt = usedITBig st
                                            , usedReadStr = usedRead st
                                            }
     )

getSwitchJs :: JsAST -> [LAlt] -> JsAST
getSwitchJs x alts =
  if any conCase alts then JsArrayProj (JsInt 0) x
    else if any constBigIntCase alts then JsForeign "%0.toString()" [x]
            else x
  where conCase (LConCase _ _ _ _) = True
        conCase _ = False
        constBigIntCase (LConstCase (BI _) _) = True
        constBigIntCase _ = False

addRT :: BodyResTarget -> JsAST -> JsAST
addRT ReturnBT x = JsReturn x
addRT (DecBT n) x = JsLet n x
addRT (SetBT n) x = JsSetVar n x
addRT (DecConstBT n) x = JsConst n x
addRT GetExpBT x = x

declareUsedOptimArgs :: Set (Text, Text) -> JsAST
declareUsedOptimArgs x = seqJs $ map (\(x,y) -> JsLet x (JsVar y) ) (Set.toList x)

tailCallOptimRefreshArgs :: [(Text, JsAST)] -> Set Text -> ((JsAST, JsAST), Set (Text, Text))
tailCallOptimRefreshArgs [] s = ((JsEmpty, JsEmpty), Set.empty)
tailCallOptimRefreshArgs ((n,x):r) s =
  let ((y1,y2), y3) = tailCallOptimRefreshArgs r (Set.insert n s) --
  in if Set.null $ (Set.fromList [ z | z <- universeBi x ]) `Set.intersection` s then
      ((y1, JsSetVar n x `JsSeq` y2), y3)
      else
        let n' = jsTailCallOptimName n
        in ((JsSetVar n' x `JsSeq` y1, JsSetVar n (JsVar n') `JsSeq` y2), Set.insert (n',n) y3)


cgBody :: BodyResTarget -> LExp -> State CGBodyState ([JsAST], JsAST)
cgBody rt (LV (Glob n)) =
  do
    argsFn <- getArgList n
    case argsFn of
      Just [] ->
        pure $ ([], addRT rt $ JsApp (jsName n) [])
      Just a ->
        do
          let part = Partial n  0  (length a)
          addPartial part
          pure ([], addRT rt $ JsApp (jsPartialName part) [])
      Nothing ->
        pure $ ([], addRT rt $ JsVar $ jsName n)
cgBody rt (LApp tailcall (LV (Glob fn)) args) =
  do
    let fname = jsName fn
    st <- get
    let (currFn, argN) = currentFnNameAndArgs st
    z <- mapM (cgBody GetExpBT) args
    let argVals = map snd z
    let preDecs = concat $ map fst z
    case (fname == currFn && (length args) == (length argN), rt) of
      (True, ReturnBT) ->
        do
          modify (\x-> x {isTailRec = True})
          let ((y1,y2), y3) = tailCallOptimRefreshArgs (zip argN argVals) Set.empty
          addUsedArgsTailCallOptim y3
          pure (preDecs, y1 `JsSeq` y2)
      _ ->
        do
          argsFn <- getArgList fn
          case argsFn of
            Nothing ->
              pure (preDecs, addRT rt $ JsCurryApp (JsVar fname) argVals )
            Just agFn ->
              do
                let lenAgFn = length agFn
                let lenArgs = length args
                case compare lenAgFn lenArgs of
                  EQ ->
                    pure (preDecs, addRT rt $ JsApp fname argVals)
                  LT ->
                    pure (preDecs, addRT rt $ JsCurryApp  (JsApp fname (take lenAgFn argVals )) (drop lenAgFn argVals) )
                  GT ->
                    do
                      let part = Partial fn lenArgs lenAgFn
                      addPartial part
                      pure (preDecs, addRT rt $ JsApp (jsPartialName part) argVals )

cgBody rt (LForce (LLazyApp n args)) = cgBody rt (LApp False (LV (Glob n)) args)
cgBody rt (LLazyApp n args) =
  do
    (d,v) <- cgBody ReturnBT (LApp False (LV (Glob n)) args)
    pure ([], addRT rt $ JsLazy $ JsSeq (seqJs d) v)
cgBody rt (LForce e) =
  do
    (d,v) <- cgBody GetExpBT e
    pure (d, addRT rt $ JsForce v)
cgBody rt (LLet n v sc) =
  do
    (d1, v1) <- cgBody (DecConstBT $ jsName n) v
    (d2, v2) <- cgBody rt sc
    pure $ ((d1 ++ v1 : d2), v2 )
cgBody rt (LProj e i) =
  do
    (d, v) <- cgBody GetExpBT e
    pure $ (d, addRT rt $ JsArrayProj (JsInt $ i+1) $ v)
cgBody rt (LCon _  conId n args) =
  do
    z <- mapM (cgBody GetExpBT) args
    pure $ (concat $ map fst z, addRT rt $ JsArray (JsInt conId : map snd z))
cgBody rt (LCase _ e alts) =
  do
    (d,v) <- cgBody GetExpBT e
    resName <- getNewCGName
    swName <- getNewCGName
    (altsJs,def) <- cgAlts rt resName (JsVar swName) alts
    let decSw = JsConst swName v
    let sw = JsSwitchCase (getSwitchJs (JsVar swName) alts) altsJs def
    case rt of
      ReturnBT ->
        pure (d ++ [decSw], sw)
      (DecBT nvar) ->
        pure (d ++ [decSw, JsLet nvar JsNull], sw)
      (SetBT nvar) ->
        pure (d ++ [decSw], sw)
      GetExpBT ->
        pure (d ++ [decSw, JsLet resName JsNull, sw], JsVar resName)
      (DecConstBT nvar) ->
        pure (d ++ [decSw, JsLet nvar JsNull], sw)
cgBody rt (LConst c) =
  do
     cst <- cgConst c
     pure ([], (addRT rt) $ cst)
cgBody rt (LOp op args) =
  do
    z <- mapM (cgBody GetExpBT) args
    res <- cgOp op (map snd z)
    pure $ (concat $ map fst z, addRT rt $ res)
cgBody rt LNothing = pure ([], addRT rt JsNull)
cgBody rt (LError x) = pure ([JsError $ JsStr x], addRT rt JsNull)
cgBody rt x@(LForeign dres (FStr code) args ) =
  do
    z <- mapM (cgBody GetExpBT) (map snd args)
    jsArgs <- sequence $ map cgForeignArg (zip (map fst args) (map snd z))
    jsDres <- cgForeignRes dres $ JsForeign (T.pack code) jsArgs
    pure $ (concat $ map fst z, addRT rt $ jsDres)
cgBody _ x = error $ "Instruction " ++ show x ++ " not compilable yet"

altsRT :: Text -> BodyResTarget -> BodyResTarget
altsRT rn ReturnBT = ReturnBT
altsRT rn (DecBT n) = SetBT n
altsRT rn (SetBT n) = SetBT n
altsRT rn (DecConstBT n) = SetBT n
altsRT rn GetExpBT = SetBT rn

cgAlts :: BodyResTarget -> Text -> JsAST -> [LAlt] -> State CGBodyState ([(JsAST, JsAST)], Maybe JsAST)
cgAlts rt resName scrvar ((LConstCase t exp):r) =
  do
    (d, v) <- cgBody (altsRT resName rt) exp
    (ar, def) <- cgAlts rt resName scrvar r
    cst <- case t of
            BI _ ->
              do
                setUsedITBig
                c' <- cgConst t
                pure $ JsForeign "%0.toString()" [c']
            _ -> cgConst t
    pure ((cst, JsSeq (seqJs d) v) : ar, def)
cgAlts rt resName scrvar ((LDefaultCase exp):r) =
  do
    (d, v) <- cgBody (altsRT resName rt) exp
    pure ([], Just $ JsSeq (seqJs d) v)
cgAlts rt resName scrvar ((LConCase _ n args exp):r) =
  do
    (d, v) <- cgBody (altsRT resName rt) exp
    (ar, def) <- cgAlts rt resName scrvar r
    conId <- getConsId n
    let replace = replaceVarsByProj scrvar (Map.fromList $ zip (map jsName args) [1..])
    let branchBody = JsSeq (seqJs $ map replace d) (replace v)
    pure ((JsInt conId, branchBody) : ar, def)
cgAlts _ _ _ [] =
  pure ([],Nothing)


cgForeignArg :: (FDesc, JsAST) -> State CGBodyState JsAST
cgForeignArg (FApp (UN "JS_IntT") _, v) = pure v
cgForeignArg (FCon (UN "JS_Str"), v) = pure v
cgForeignArg (FCon (UN "JS_Ptr"), v) = pure v
cgForeignArg (FCon (UN "JS_Unit"), v) = pure v
cgForeignArg (FApp (UN "JS_FnT") [_,FApp (UN "JS_Fn") [_,_, a, FApp (UN "JS_FnBase") [_,b]]], f) =
  pure f
cgForeignArg (FApp (UN "JS_FnT") [_,FApp (UN "JS_Fn") [_,_, a, FApp (UN "JS_FnIO") [_,_, b]]], f) =
  do
    jsx <- cgForeignArg (a, JsVar "x")
    jsres <- cgForeignRes b $ JsCurryApp (JsCurryApp f [jsx]) [JsNull]
    pure $ JsLambda ["x"] $ JsReturn jsres
cgForeignArg (desc, _) =
  do
    st <- get
    error $ "Foreign arg type " ++ show desc ++ " not supported. While generating function " ++ (show $ fst $ currentFnNameAndArgs st)

cgForeignRes :: FDesc -> JsAST -> State CGBodyState JsAST
cgForeignRes (FApp (UN "JS_IntT") _) x = pure x
cgForeignRes (FCon (UN "JS_Unit")) x = pure x
cgForeignRes (FCon (UN "JS_Str")) x = pure x
cgForeignRes (FCon (UN "JS_Ptr")) x = pure x
cgForeignRes (FCon (UN "JS_Float")) x = pure x
--cgForeignRes _ x = x
cgForeignRes desc val =
  do
    st <- get
    error $ "Foreign return type " ++ show desc ++ " not supported. While generating function " ++ (show $ fst $ currentFnNameAndArgs st)

setUsedITBig :: State CGBodyState ()
setUsedITBig =   modify (\s -> s {usedITBig = True})


cgConst :: Const -> State CGBodyState JsAST
cgConst (I i) = pure $ JsInt i
cgConst (BI i) =
  do
    setUsedITBig
    pure $ JsForeign "new jsbn.BigInteger(%0)" [JsStr $ show i]
cgConst (Ch c) = pure $ JsStr [c]
cgConst (Str s) = pure $ JsStr s
cgConst (Fl f) = pure $ JsNum f
cgConst (B8 x) = error "error B8"
cgConst (B16 x) = error "error B16"
cgConst (B32 x) = error "error B32"
cgConst (B64 x) = error "error B64"
cgConst x | isTypeConst x = pure $ JsInt 0
cgConst x = error $ "Constant " ++ show x ++ " not compilable yet"

jsB2I :: JsAST -> JsAST
jsB2I x = JsForeign "%0 ? 1|0 : 0|0" [x]

cgOp :: PrimFn -> [JsAST] -> State CGBodyState JsAST
cgOp (LPlus ATFloat) [l, r] = pure $ JsBinOp "+" l r
cgOp (LPlus (ATInt ITNative)) [l, r] = pure $ JsForeign "%0+%1|0" [l,r]
cgOp (LPlus (ATInt ITBig)) [l, r] =
  do
    setUsedITBig
    pure $ JsMethod l "add" [r]
cgOp (LMinus ATFloat) [l, r] = pure $ JsBinOp "-" l r
cgOp (LMinus (ATInt ITNative)) [l, r] = pure $ JsForeign "%0-%1|0" [l,r]
cgOp (LMinus (ATInt ITBig)) [l, r] =
  do
    setUsedITBig
    pure $ JsMethod l "subtract" [r]
cgOp (LTimes ATFloat) [l, r] = pure $ JsBinOp "*" l r
cgOp (LTimes (ATInt ITNative)) [l, r] = pure $ JsForeign "%0*%1|0" [l,r]
cgOp (LTimes (ATInt ITBig)) [l, r] =
  do
    setUsedITBig
    pure $ JsMethod l "multiply" [r]
cgOp (LEq ATFloat) [l, r] = pure $ jsB2I $ JsBinOp "==" l r
cgOp (LEq (ATInt ITNative)) [l, r] = pure $ jsB2I $ JsBinOp "==" l r
cgOp (LEq (ATInt ITChar)) [l,r] = pure $ jsB2I $ JsBinOp "==" l r
cgOp (LEq (ATInt ITBig)) [l, r] =
  do
    setUsedITBig
    pure $ jsB2I $ JsMethod l "equals" [r]
cgOp (LSLt ATFloat) [l, r] = pure $ jsB2I $ JsBinOp "<" l r
cgOp (LSLt (ATInt ITChar)) [l, r] = pure $ jsB2I $ JsBinOp "<" l r
cgOp (LSLt (ATInt ITNative)) [l, r] = pure $ jsB2I $ JsBinOp "<" l r
cgOp (LSLt (ATInt ITBig)) [l, r] =
  do
    setUsedITBig
    pure $ jsB2I $ JsForeign "%0.compareTo(%1) < 0" [l,r]
cgOp (LSLe ATFloat) [l, r] = pure $ jsB2I $ JsBinOp "<=" l r
cgOp (LSLe (ATInt ITNative)) [l, r] = pure $ jsB2I $ JsBinOp "<=" l r
cgOp (LSLe (ATInt ITBig)) [l, r] =
  do
    setUsedITBig
    pure $ jsB2I $ JsForeign "%0.compareTo(%1) <= 0" [l,r]
cgOp (LSGt ATFloat) [l, r] = pure $ jsB2I $ JsBinOp ">" l r
cgOp (LSGt (ATInt ITNative)) [l, r] = pure $ jsB2I $ JsBinOp ">" l r
cgOp (LSGt (ATInt ITBig)) [l, r] =
  do
    setUsedITBig
    pure $ jsB2I $ JsForeign "%0.compareTo(%1) > 0" [l,r]
cgOp (LSGe ATFloat) [l, r] = pure $ jsB2I $ JsBinOp ">=" l r
cgOp (LSGe (ATInt ITNative)) [l, r] = pure $ jsB2I $ JsBinOp ">=" l r
cgOp (LSGe (ATInt ITBig)) [l, r] =
  do
    setUsedITBig
    pure $ jsB2I $ JsForeign "%0.compareTo(%1) >= 0" [l,r]
cgOp LStrEq [l,r] = pure $ jsB2I $ JsBinOp "==" l r
cgOp LStrLen [x] = pure $ JsForeign "%0.length" [x]
cgOp LStrHead [x] = pure $ JsArrayProj (JsInt 0) x
cgOp LStrIndex [x, y] = pure $ JsArrayProj y x
cgOp LStrTail [x] = pure $ JsMethod x "slice" [JsInt 1]
cgOp LStrLt [l, r] = pure $ jsB2I $ JsBinOp "<" l r
cgOp LStrRev [x] = pure $ JsForeign "%0.split('').reverse().join('')" [x]
cgOp (LFloatStr) [x] = pure $ JsApp "String" [x]
cgOp (LIntStr ITNative) [x] = pure $  JsApp "String" [x]
cgOp (LIntStr ITBig) [x] =
  do
    setUsedITBig
    pure $ JsForeign "%0.toString()" [x]
cgOp (LFloatInt ITNative) [x] = pure $ JsForeign "%x|0" [x]
cgOp (LStrInt ITNative) [x] = pure $ JsForeign "parseInt(%0)|0" [x]
cgOp (LStrFloat) [x] = pure $ JsApp "parseFloat" [x]
cgOp (LChInt ITNative) [x] = pure $ JsForeign "%0.charCodeAt(0)|0" [x]
cgOp (LIntCh ITNative) [x] = pure $ JsApp "String.fromCharCode" [x]
cgOp (LTrunc ITBig ITNative) [x] = pure $ JsForeign "%0.intValue()|0" [x]
cgOp (LSExt ITNative ITBig) [x] =
  do
    setUsedITBig
    pure $ JsForeign "new jsbn.BigInteger(String(%0))" [x]
cgOp (LZExt ITNative ITBig) [x] =
  do
    setUsedITBig
    pure $ JsForeign "new jsbn.BigInteger(String(%0))" [x]
--cgOp (LZExt _ _) [x] = pure $ x
cgOp (LIntFloat ITNative) [x] = pure $ x
cgOp (LSDiv (ATInt ITNative)) [l,r] = pure $ JsForeign "%0/%1|0" [l, r]
cgOp (LSDiv (ATInt ITBig)) [l,r] =
  do
    setUsedITBig
    pure $ JsMethod l "divide" [r]
cgOp LWriteStr [_,str] =
  do
    s <- get
    put $ s {usedWrite = True}
    pure $ JsForeign (writeStrTemplate $ conf s) [str]
cgOp LReadStr [_] =
  do
    s <- get
    put $ s {usedRead = True}
    pure $ JsForeign (readStrTemplate $ conf s) []
cgOp LStrConcat [l,r] = pure $ JsBinOp "+" l r
cgOp LStrCons [l,r] = pure $ JsForeign "%0+%1" [l,r]
cgOp LStrSubstr [offset,len,str] = pure $  JsMethod str "substr" [offset, len]
cgOp (LSRem (ATInt ITNative)) [l,r] = pure $ JsBinOp "%" l r
cgOp LCrash [l] = pure $ JsErrorExp l
cgOp op exps = error ("Operator " ++ show (op, exps) ++ " not implemented")
