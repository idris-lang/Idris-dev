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

import Data.Maybe (fromJust)
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import Data.Char
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.List (nub)
import System.Directory (doesFileExist)
import System.FilePath (combine)
import Control.Monad.Trans.State
import System.Environment

import GHC.Generics (Generic)
import Data.Data
import Data.Generics.Uniplate.Data
import Data.List

data CGStats = CGStats { usedWriteStr :: Bool
                       }

emptyStats :: CGStats
emptyStats = CGStats {usedWriteStr = False}

data CGConf = CGConf { header :: Text
                     , footer :: Text
                     , initialization :: CGStats -> Text
                     , writeStrTemplate :: Text
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
    let defs = addAlist (liftDecls ci) emptyContext
    let used = used_decls defs [sMN 0 "runMain"]
    used `deepseq` if debug then
      do
        putStrLn $ "Finished calculating used"
        writeFile (outputFile ci ++ ".LDeclsDebug") $ (unlines $ intersperse "" $ map show used) ++ "\n\n\n"
      else pure ()

    let (out, stats) = doCodegen conf defs used --T.intercalate "\n" $ map (doCodegen conf defs) used
    out `deepseq` if debug then putStrLn $ "Finished generating code" else pure ()
    includes <- get_includes $ includes ci
    TIO.writeFile (outputFile ci) $ T.concat [ header conf
                                             , "\"use strict\";\n\n"
                                             , "(function(){\n\n"
                                             , initialization conf stats
                                             , includes, "\n"
                                             , js_aux_defs, "\n"
                                             , out, "\n"
                                             , "\n"
                                             , jsName (sMN 0 "runMain"), "();\n\n"
                                             , "\n}())"
                                             , footer conf
                                             ]

jsName :: Name -> Text
jsName n = T.pack $ "idris_" ++ concatMap jschar (showCG n)
  where jschar x | isAlpha x || isDigit x = [x]
                  | otherwise = "_" ++ show (fromEnum x) ++ "_"

doCodegen :: CGConf -> LDefs -> [LDecl] -> (Text, CGStats)
doCodegen conf defs decls =
  let xs = map (doCodegenDecl conf defs) decls
      groupCGStats x y = CGStats {usedWriteStr = usedWriteStr x || usedWriteStr y}
  in (T.intercalate "\n" $ map fst xs, foldl' groupCGStats emptyStats (map snd xs) )

doCodegenDecl :: CGConf -> LDefs -> LDecl -> (Text, CGStats)
doCodegenDecl conf defs (LFun _ n args def) =
  let (ast, stats) = cgFun conf defs n args def
  in (jsAst2Text $ ast, stats)
doCodegenDecl conf defs (LConstructor n i sz) =
  ("", emptyStats)

seqJs :: [JsAST] -> JsAST
seqJs [] = JsEmpty
seqJs (x:xs) = JsSeq x (seqJs xs)

data CGBodyState = CGBodyState { defs :: LDefs
                               , lastIntName :: Int
                               , currentFnNameAndArgs :: (Text, [Text])
                               , isTailRec :: Bool
                               , conf :: CGConf
                               , usedWrite :: Bool
                               }

getNewCGName :: State CGBodyState Text
getNewCGName =
  do
    st <- get
    let v = lastIntName st + 1
    put $ st {lastIntName = v}
    return $ T.pack $ "cgIdris_" ++ show v

getNewCGNames :: Int -> State CGBodyState [Text]
getNewCGNames n =
  mapM (\_ -> getNewCGName) [1..n]

getConsId :: Name -> State CGBodyState Int
getConsId n =
    do
      st <- get
      case lookupCtxtExact n (defs st) of
        Just (LConstructor _ conId _) -> pure conId
        _ -> error $ "Internal JS Backend error " ++ showCG n ++ " is not a constructor."

getArgList :: Name -> State CGBodyState (Maybe [Name])
getArgList n =
  do
    st <- get
    case lookupCtxtExact n (defs st) of
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

cgFun :: CGConf -> LDefs -> Name -> [Name] -> LExp -> (JsAST, CGStats)
cgFun cnf dfs n args def =
  let
      fnName = jsName n
      argNames = map jsName args
      ((decs, res),st) = runState
                          (cgBody ReturnBT def)
                          (CGBodyState { defs=dfs
                                       , lastIntName = 0
                                       , currentFnNameAndArgs = (fnName, argNames)
                                       , isTailRec = False
                                       , conf = cnf
                                       , usedWrite = False
                                       }
                          )
      body = if isTailRec st then
                JsFor (JsLetList [("cgArgs", JsApp "Array.prototype.slice.call" [JsVar "arguments"]), ("cgArgs2", JsNull) ] , JsTrue, JsSetVar  "cgArgs" (JsVar "cgArgs2")  ) $
                --JsSeq (JsDecVar "cgArgs" $ JsApp "Array.prototype.slice.call" [JsVar "arguments"]) $ JsWhileTrue $
                  replaceVarsByProj
                    (JsVar "cgArgs")
                    (Map.fromList $ zip argNames [0..])
                    ((seqJs decs) `JsSeq` res)
                else JsSeq (seqJs decs) res
  in (JsFun fnName argNames $ body, CGStats {usedWriteStr = usedWrite st})

getSwitchJs :: JsAST -> [LAlt] -> JsAST
getSwitchJs x alts =
  if any conCase alts then JsArrayProj (JsInt 0) x
    else x
  where conCase (LConCase _ _ _ _) = True
        conCase _ = False

addRT :: BodyResTarget -> JsAST -> JsAST
addRT ReturnBT x = JsReturn x
addRT (DecBT n) x = JsLet n x
addRT (SetBT n) x = JsSetVar n x
addRT (DecConstBT n) x = JsConst n x
addRT GetExpBT x = x

cgBody :: BodyResTarget -> LExp -> State CGBodyState ([JsAST], JsAST)
cgBody rt (LV (Glob n)) =
  do
    argsFn <- getArgList n
    case argsFn of
      Just [] ->
        pure $ ([], addRT rt $ JsApp (jsName n) [])
      Just a ->
        do
          newNames <- getNewCGNames $ length a
          pure ([], addRT rt $ JsCurryLambda newNames (JsApp (jsName n) (map JsVar newNames)))
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
          --vars <- getNewCGNames $ length argN --sequence $ map (\_->getNewCGName) argN
          let refreshArgs = JsSetVar "cgArgs2" (JsArray argVals)
          --let calcs = map (\(n,v) -> JsDecVar n v) (zip vars argVals)
          --let calcsToArgs = map (\(n,v) -> JsSetVar n (JsVar v)) (zip argN vars)
          pure (preDecs, refreshArgs)
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
                      newNames <- getNewCGNames $ lenAgFn - lenArgs
                      pure (preDecs, addRT rt $ JsCurryLambda newNames (JsApp fname (argVals ++ (map JsVar newNames) )  ) )

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
cgBody rt (LConst c) = pure ([], (addRT rt) $ cgConst c)
cgBody rt (LOp op args) =
  do
    z <- mapM (cgBody GetExpBT) args
    res <- cgOp op (map snd z)
    pure $ (concat $ map fst z, addRT rt $ res)
cgBody rt LNothing = pure ([], addRT rt JsNull)
cgBody rt (LError x) = pure ([JsError $ JsStr $ T.pack $ x], addRT rt JsNull)
cgBody rt x@(LForeign dres (FStr code) args ) =
  do
    z <- mapM (cgBody GetExpBT) (map snd args)
    let jsArgs = map cgForeignArg (zip (map fst args) (map snd z))
    pure $ (concat $ map fst z, addRT rt $ cgForeignRes dres $ JsForeign (T.pack code) jsArgs)
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
    pure ((cgConst t, JsSeq (seqJs d) v) : ar, def)
cgAlts rt resName scrvar ((LDefaultCase exp):r) =
  do
    (d, v) <- cgBody (altsRT resName rt) exp
    pure ([], Just $ JsSeq (seqJs d) v)
cgAlts rt resName scrvar ((LConCase _ n args exp):r) =
  do
    (d, v) <- cgBody (altsRT resName rt) exp
    (ar, def) <- cgAlts rt resName scrvar r
    conId <- getConsId n
    -- let branchBody = JsSeq (conCaseToProjs 1 scrvar args) $ JsSeq (seqJs d) v
    let replace = replaceVarsByProj scrvar (Map.fromList $ zip (map jsName args) [1..])
    let branchBody = JsSeq (seqJs $ map replace d) (replace v)
    pure ((JsInt conId, branchBody) : ar, def)
cgAlts _ _ _ [] =
  pure ([],Nothing)


cgForeignArg :: (FDesc, JsAST) -> JsAST
cgForeignArg (FApp (UN "JS_IntT") _, v) = v
cgForeignArg (FCon (UN "JS_Str"), v) = v
cgForeignArg (FCon (UN "JS_Ptr"), v) = v
cgForeignArg (FCon (UN "JS_Unit"), v) = v
cgForeignArg (FApp (UN "JS_FnT") [_,FApp (UN "JS_Fn") [_,_, a, FApp (UN "JS_FnBase") [_,b]]], f) =
  f
cgForeignArg (FApp (UN "JS_FnT") [_,FApp (UN "JS_Fn") [_,_, a, FApp (UN "JS_FnIO") [_,_, b]]], f) =
  JsLambda ["x"] $ JsReturn $ cgForeignRes b $ JsCurryApp (JsCurryApp f [cgForeignArg (a, JsVar "x")]) [JsNull]
cgForeignArg (desc, _) = error $ "Foreign arg type " ++ show desc ++ " not supported yet."

cgForeignRes :: FDesc -> JsAST -> JsAST
cgForeignRes (FApp (UN "JS_IntT") _) x = x
cgForeignRes (FCon (UN "JS_Unit")) x = x
cgForeignRes (FCon (UN "JS_Str")) x = x
cgForeignRes (FCon (UN "JS_Ptr")) x =  x
cgForeignRes (FCon (UN "JS_Float")) x = x
cgForeignRes desc val =  error $ "Foreign return type " ++ show desc ++ " not supported yet."

cgConst :: Const -> JsAST
cgConst (I i) = JsInt i
cgConst (BI i) = JsInteger i
cgConst (Ch c) = JsInt $ ord c
cgConst (Str s) = JsStr $ T.pack s
cgConst (Fl f) = JsDouble f
cgConst (B8 x) = error "error B8"
cgConst (B16 x) = error "error B16"
cgConst (B32 x) = error "error B32"
cgConst (B64 x) = error "error B64"
cgConst x | isTypeConst x = JsInt 0
cgConst x = error $ "Constant " ++ show x ++ " not compilable yet"

cgOp :: PrimFn -> [JsAST] -> State CGBodyState JsAST
cgOp (LPlus _) [l, r] = pure $ JsBinOp "+" l r
cgOp (LMinus _) [l, r] = pure $ JsBinOp "-" l r
cgOp (LTimes _) [l, r] = pure $ JsBinOp "*" l r
cgOp (LEq _) [l, r] = pure $ JsB2I $ JsBinOp "==" l r
cgOp (LSLt _) [l, r] = pure $ JsB2I $ JsBinOp "<" l r
cgOp (LSLe _) [l, r] = pure $ JsB2I $ JsBinOp "<=" l r
cgOp (LSGt _) [l, r] = pure $ JsB2I $ JsBinOp ">" l r
cgOp (LSGe _) [l, r] = pure $ JsB2I $ JsBinOp ">=" l r
cgOp LStrEq [l,r] = pure $ JsB2I $ JsBinOp "==" l r
cgOp LStrLen [x] = pure $ JsForeign "%0.length" [x]
cgOp LStrHead [x] = pure $ JsMethod x "charCodeAt" [JsInt 0]
cgOp LStrIndex [x, y] = pure $ JsMethod x "charCodeAt" [y]
cgOp LStrTail [x] = pure $ JsMethod x "slice" [JsInt 1]
cgOp LStrLt [l, r] = pure $ JsB2I $ JsBinOp "<" l r
cgOp (LFloatStr) [x] = pure $ JsBinOp "+" x (JsStr "")
cgOp (LIntStr _) [x] = pure $ JsBinOp "+" x (JsStr "")
cgOp (LFloatInt _) [x] = pure $ JsApp "Math.trunc" [x]
cgOp (LStrInt _) [x] = pure $ JsBinOp "||" (JsApp "parseInt" [x]) (JsInt 0)
cgOp (LStrFloat) [x] = pure $ JsBinOp "||" (JsApp "parseFloat" [x]) (JsInt 0)
cgOp (LChInt _) [x] = pure $ x
cgOp (LIntCh _) [x] = pure $ x
cgOp (LSExt _ _) [x] = pure $ x
cgOp (LZExt _ _) [x] = pure $ x
cgOp (LIntFloat _) [x] = pure $ x
cgOp (LSDiv _) [x,y] = pure $ JsBinOp "/" x y
cgOp LWriteStr [_,str] =
  do
    s <- get
    put $ s {usedWrite = True}
    pure $ JsForeign (writeStrTemplate $ conf s) [str]
    --pure $ JsApp "console.log" [str]
cgOp LStrConcat [l,r] = pure $ JsBinOp "+" l r
cgOp LStrCons [l,r] = pure $ JsForeign "String.fromCharCode(%0) + %1" [l,r]
cgOp (LSRem (ATInt _)) [l,r] = pure $ JsBinOp "%" l r
cgOp LCrash [l] = pure $ JsErrorExp l
cgOp op exps = error ("Operator " ++ show (op, exps) ++ " not implemented")
