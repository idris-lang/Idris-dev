{-|
Module      : IRTS.JavaScript.Codegen
Description : The JavaScript common code generator.

License     : BSD3
Maintainer  : The Idris Community.
-}
{-# LANGUAGE CPP, OverloadedStrings #-}

module IRTS.JavaScript.Codegen( codegenJs
                              , CGConf(..)
                              , CGStats(..)
                              ) where

import Idris.Core.TT
import IRTS.CodegenCommon
import IRTS.Exports
import IRTS.JavaScript.AST
import IRTS.JavaScript.LangTransforms
import IRTS.JavaScript.Name
import IRTS.JavaScript.PrimOp
import IRTS.JavaScript.Specialize
import IRTS.Lang
import IRTS.System

import Control.Applicative (pure, (<$>))
import Control.Monad
import Control.Monad.Trans.State
import Data.Foldable (foldMap)
import Data.Generics.Uniplate.Data
import Data.List
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import System.Directory (doesFileExist)
import System.Environment
import System.FilePath

-- | Code generation stats hold information about the generated user
-- code. Based on that information we add additional code to make
-- things work.
data CGStats = CGStats { usedBigInt :: Bool
                       , partialApplications :: Set Partial
                       , hiddenClasses :: Set HiddenClass
                       }

#if (MIN_VERSION_base(4,11,0))
instance Semigroup CGStats where
    (<>) = mappend
#endif

-- If we generate code for two declarations we want to merge their code
-- generation stats.
instance Monoid CGStats where
  mempty = CGStats { partialApplications = Set.empty
                   , hiddenClasses = Set.empty
                   , usedBigInt = False
                   }
  mappend x y = CGStats { partialApplications = partialApplications x `Set.union` partialApplications y
                        , hiddenClasses = hiddenClasses x `Set.union` hiddenClasses y
                        , usedBigInt = usedBigInt x || usedBigInt y
                        }


data CGConf = CGConf { header :: Text
                     , footer :: Text
                     , jsbnPath :: String
                     , extraRunTime :: String
                     }


getInclude :: FilePath -> IO Text
getInclude p =
  do
    libs <- getIdrisLibDir
    let libPath = libs </> p
    exitsInLib <- doesFileExist libPath
    if exitsInLib then
      TIO.readFile libPath
      else TIO.readFile p

getIncludes :: [FilePath] -> IO Text
getIncludes l = do
  incs <- mapM getInclude l
  return $ T.intercalate "\n\n" incs

includeLibs :: [String] -> String
includeLibs =
  let
    repl '\\' = '_'
    repl '/' = '_'
    repl '.' = '_'
    repl '-' = '_'
    repl c   = c
  in
    concatMap (\lib -> "var " ++ (repl <$> lib) ++ " = require(\"" ++ lib ++"\");\n")

isYes :: Maybe String -> Bool
isYes (Just "Y") = True
isYes (Just "y") = True
isYes _ = False

makeExportDecls :: Map Name LDecl -> ExportIFace -> [Text]
makeExportDecls defs (Export _ _ e) =
  concatMap makeExport e
  where
    uncurryF name argTy (Just args) retTy =
      if length argTy == length args then
          case (retTy, length args) of
            (FIO _, 0) -> T.concat ["function(){return ", name, "()()}"]
            _ -> name
        else T.concat [ "function(){ return "
                      , name
                      , ".apply(this, Array.prototype.slice.call(arguments, 0,", T.pack $ show $ length args,"))"
                      , T.concat $ map (\x -> T.concat ["(arguments[", T.pack $ show x , "])"]) [length args .. (length argTy - 1)]
                      , "}"
                      ]
    uncurryF name argTy Nothing retTy = name

    makeExport (ExportData _) =
      []
    makeExport (ExportFun name (FStr exportname) retTy argTy) =
      [T.concat [ T.pack $ exportname
                ,  ": "
                , uncurryF (jsName name) argTy (getArgList' name defs) retTy
                ]
      ]

codegenJs :: CGConf -> CodeGenerator
codegenJs conf ci =
  do
    debug <- isYes <$> lookupEnv "IDRISJS_DEBUG"
    let defs' = Map.fromList $ liftDecls ci
    let defs = globlToCon defs'
    let iface = interfaces ci
    let used = if iface then
                  Map.elems $ removeDeadCode defs (getExpNames $ exportDecls ci)
                  else Map.elems $ removeDeadCode defs [sMN 0 "runMain"]
    when debug $ do
        writeFile (outputFile ci ++ ".LDeclsDebug") $ (unlines $ intersperse "" $ map show used) ++ "\n\n\n"
        putStrLn $ "Finished calculating used"

    let (out, stats) = doCodegen defs used

    path <- getIdrisJSRTSDir
    jsbn <- if usedBigInt stats
              then TIO.readFile $ path </> jsbnPath conf
              else return ""

    runtimeCommon <- TIO.readFile $ path </> "Runtime-common.js"
    extraRT <- TIO.readFile $ path </> (extraRunTime conf)

    includes <- getIncludes $ includes ci
    let libs = T.pack $ includeLibs $ compileLibs ci
    TIO.writeFile (outputFile ci) $ T.concat [ header conf
                                             , "\"use strict\";\n\n"
                                             , "(function(){\n\n"
                                             -- rts
                                             , runtimeCommon, "\n"
                                             , extraRT, "\n"
                                             , jsbn, "\n"
                                             -- external libraries
                                             , includes, "\n"
                                             , libs, "\n"
                                             -- user code
                                             , doPartials (partialApplications stats), "\n"
                                             , doHiddenClasses (hiddenClasses stats), "\n"
                                             , out, "\n"
                                             , if iface then T.concat ["module.exports = {\n", T.intercalate ",\n" $ concatMap (makeExportDecls defs) (exportDecls ci), "\n};\n"]
                                                  else jsName (sMN 0 "runMain") `T.append` "();\n"
                                             , "}.call(this))"
                                             , footer conf
                                             ]

doPartials :: Set Partial -> Text
doPartials x =
  T.intercalate "\n" (map f $ Set.toList x)
  where
      f p@(Partial n i j) =
        let vars1 = map (T.pack . ("x"++) . show) [1..i]
            vars2 = map (T.pack . ("x"++) . show) [(i+1)..j]
        in jsStmt2Text $
             JsFun (jsNamePartial p) vars1 $ JsReturn $
               jsCurryLam vars2 (jsAppN (jsName n) (map JsVar (vars1 ++ vars2)) )

doHiddenClasses :: Set HiddenClass -> Text
doHiddenClasses x =
  T.intercalate "\n" (map f $ Set.toList x)
  where
      f p@(HiddenClass n id 0) = jsStmt2Text $ JsDecConst (jsNameHiddenClass p) $ JsObj [("type", JsInt id)]
      f p@(HiddenClass n id arity) =
        let vars = map dataPartName $ take arity [1..]
        in jsStmt2Text $
             JsFun (jsNameHiddenClass p) vars $ JsSeq (JsSet (JsProp JsThis "type") (JsInt id)) $ seqJs
               $ map (\tv -> JsSet (JsProp JsThis tv) (JsVar tv)) vars


-- | Generate code for each declaration and collect stats.
-- LFunctions are turned into JS function declarations. They are
-- preceded by a comment that gives their name. Constructor
-- declarations are ignored.
doCodegen :: Map Name LDecl -> [LDecl] -> (Text, CGStats)
doCodegen defs = foldMap (doCodegenDecl defs)
  where
    doCodegenDecl :: Map Name LDecl -> LDecl -> (Text, CGStats)
    doCodegenDecl defs (LFun _ name args def) =
      let (ast, stats) = cgFun defs name args def
          fnComment = jsStmt2Text (JsComment $ T.pack $ show name)
      in (T.concat [fnComment, "\n", jsStmt2Text ast, "\n"], stats)
    doCodegenDecl defs (LConstructor n i sz) = ("", mempty)


seqJs :: [JsStmt] -> JsStmt
seqJs [] = JsEmpty
seqJs (x:xs) = JsSeq x (seqJs xs)


data CGBodyState = CGBodyState { defs :: Map Name LDecl
                               , lastIntName :: Int
                               , reWrittenNames :: Map.Map Name JsExpr
                               , currentFnNameAndArgs :: (Text, [Text])
                               , usedArgsTailCallOptim :: Set (Text, Text)
                               , isTailRec :: Bool
                               , usedITBig :: Bool
                               , partialApps :: Set Partial
                               , hiddenCls :: Set HiddenClass
                               }

getNewCGName :: State CGBodyState Text
getNewCGName =
  do
    st <- get
    let v = lastIntName st + 1
    put $ st {lastIntName = v}
    return $ jsNameGenerated v

addPartial :: Partial -> State CGBodyState ()
addPartial p =
  modify (\s -> s {partialApps = Set.insert p (partialApps s) })

addHiddenClass :: HiddenClass -> State CGBodyState ()
addHiddenClass p =
  modify (\s -> s {hiddenCls = Set.insert p (hiddenCls s) })

addUsedArgsTailCallOptim :: Set (Text, Text) -> State CGBodyState ()
addUsedArgsTailCallOptim p =
  modify (\s -> s {usedArgsTailCallOptim = Set.union p (usedArgsTailCallOptim s) })

getConsId :: Name -> State CGBodyState (Int, Int)
getConsId n =
    do
      st <- get
      case Map.lookup n (defs st) of
        Just (LConstructor _ conId arity) -> pure (conId, arity)
        _ -> error $ "Internal JS Backend error " ++ showCG n ++ " is not a constructor."

getArgList' :: Name -> Map Name LDecl -> Maybe [Name]
getArgList' n defs =
    case Map.lookup n defs of
      Just (LFun _ _ a _) -> Just a
      _ -> Nothing

getArgList :: Name -> State CGBodyState (Maybe [Name])
getArgList n =
  do
    st <- get
    pure $ getArgList' n (defs st)

data BodyResTarget = ReturnBT
                   | DecBT Text
                   | SetBT Text
                   | DecConstBT Text
                   | GetExpBT

cgFun :: Map Name LDecl -> Name -> [Name] -> LExp -> (JsStmt, CGStats)
cgFun dfs n args def = do
  let fnName = jsName n
  let argNames = map jsName args
  let ((decs, res),st) = runState
                          (cgBody ReturnBT def)
                          (CGBodyState { defs = dfs
                                       , lastIntName = 0
                                       , reWrittenNames = Map.empty
                                       , currentFnNameAndArgs = (fnName, argNames)
                                       , usedArgsTailCallOptim = Set.empty
                                       , isTailRec = False
                                       , usedITBig = False
                                       , partialApps = Set.empty
                                       , hiddenCls = Set.empty
                                       }
                          )
  let body = if isTailRec st then JsSeq (declareUsedOptimArgs $ usedArgsTailCallOptim st) (JsForever ((seqJs decs) `JsSeq` res)) else (seqJs decs) `JsSeq` res
  let fn = JsFun fnName argNames body
  let state' = CGStats { partialApplications = partialApps st
                       , hiddenClasses = hiddenCls st
                       , usedBigInt = usedITBig st
                       }
  (fn, state')

addRT :: BodyResTarget -> JsExpr -> JsStmt
addRT ReturnBT x = JsReturn x
addRT (DecBT n) x = JsDecLet n x
addRT (DecConstBT n) x = JsDecConst n x
addRT (SetBT n) x = JsSet (JsVar n) x
addRT GetExpBT x = JsExprStmt x

declareUsedOptimArgs :: Set (Text, Text) -> JsStmt
declareUsedOptimArgs x = seqJs $ map (\(x,y) -> JsDecLet x (JsVar y) ) (Set.toList x)

tailCallOptimRefreshArgs :: [(Text, JsExpr)] -> Set Text -> ((JsStmt, JsStmt), Set (Text, Text))
tailCallOptimRefreshArgs [] s = ((JsEmpty, JsEmpty), Set.empty)
tailCallOptimRefreshArgs ((n,x):r) s =
  let ((y1,y2), y3) = tailCallOptimRefreshArgs r (Set.insert n s) --
  in if Set.null $ (Set.fromList [ z | z <- universeBi x ]) `Set.intersection` s then
      ((y1, jsSetVar n x `JsSeq` y2), y3)
      else
        let n' = jsTailCallOptimName n
        in ((jsSetVar n' x `JsSeq` y1, jsSetVar n (JsVar n') `JsSeq` y2), Set.insert (n',n) y3)

cgName :: Name -> State CGBodyState JsExpr
cgName b = do
  st <- get
  case Map.lookup b (reWrittenNames st) of
    Just e -> pure e
    _ -> pure $ JsVar $ jsName b

cgBody :: BodyResTarget -> LExp -> State CGBodyState ([JsStmt], JsStmt)
cgBody rt expr =
  case expr of
    (LCase _ (LOp oper [x, y]) [LConstCase (I 0) (LCon _ _ ff []), LDefaultCase (LCon _ _ tt [])])
      | (ff == qualifyN "Prelude.Bool" "False" &&
         tt == qualifyN "Prelude.Bool" "True") ->
        case (Map.lookup oper primDB) of
          Just (needBI, pti, c) | pti == PTBool -> do
            z <- mapM (cgBody GetExpBT) [x, y]
            when needBI setUsedITBig
            let res = jsPrimCoerce pti PTBool $ c $ map (jsStmt2Expr . snd) z
            pure $ (concat $ map fst z, addRT rt res)
          _ -> cgBody' rt expr
    (LCase _ e [LConCase _ n _ (LCon _ _ tt []), LDefaultCase (LCon _ _ ff [])])
      | (ff == qualifyN "Prelude.Bool" "False" &&
         tt == qualifyN "Prelude.Bool" "True") -> do
           (d, v) <- cgBody GetExpBT e
           test <- formConTest n (jsStmt2Expr v)
           pure $ (d, addRT rt $ JsUniOp (T.pack "!") $ JsUniOp (T.pack "!") test)
    (LCase _ e [LConCase _ n _ (LCon _ _ tt []), LConCase _ _ _ (LCon _ _ ff [])])
      | (ff == qualifyN "Prelude.Bool" "False" &&
         tt == qualifyN "Prelude.Bool" "True") -> do
           (d, v) <- cgBody GetExpBT e
           test <- formConTest n (jsStmt2Expr v)
           pure $ (d, addRT rt $ JsUniOp (T.pack "!") $ JsUniOp (T.pack "!") test)
    (LCase _ e [LConCase _ n _ (LCon _ _ ff []), LDefaultCase (LCon _ _ tt [])])
      | (ff == qualifyN "Prelude.Bool" "False" &&
         tt == qualifyN "Prelude.Bool" "True") -> do
           (d, v) <- cgBody GetExpBT e
           test <- formConTest n (jsStmt2Expr v)
           pure $ (d, addRT rt $ JsUniOp (T.pack "!") test)
    (LCase _ e [LConCase _ n _ (LCon _ _ ff []), LConCase _ _ _ (LCon _ _ tt [])])
      | (ff == qualifyN "Prelude.Bool" "False" &&
         tt == qualifyN "Prelude.Bool" "True") -> do
           (d, v) <- cgBody GetExpBT e
           test <- formConTest n (jsStmt2Expr v)
           pure $ (d, addRT rt $ JsUniOp (T.pack "!") test)
    (LCase f e [LConCase nf ff [] alt, LConCase nt tt [] conseq])
      | (ff == qualifyN "Prelude.Bool" "False" &&
         tt == qualifyN "Prelude.Bool" "True") ->
        cgBody' rt $ LCase f e [LConCase nt tt [] conseq, LConCase nf ff [] alt]
    expr -> cgBody' rt expr

cgBody' :: BodyResTarget -> LExp -> State CGBodyState ([JsStmt], JsStmt)
cgBody' rt (LV n) =
  do
    argsFn <- getArgList n
    case argsFn of
      Just a -> cgBody' rt (LApp False (LV n) [])
      Nothing -> do
        n' <- cgName n
        pure $ ([], addRT rt n')
cgBody' rt (LApp tailcall (LV fn) args) =
  do
    let fname = jsName fn
    st <- get
    let (currFn, argN) = currentFnNameAndArgs st
    z <- mapM (cgBody GetExpBT) args
    let argVals = map (jsStmt2Expr . snd) z
    let preDecs = concat $ map fst z
    case (fname == currFn && (length args) == (length argN), rt) of
      (True, ReturnBT) ->
        do
          modify (\x-> x {isTailRec = True})
          let ((y1,y2), y3) = tailCallOptimRefreshArgs (zip argN argVals) Set.empty
          addUsedArgsTailCallOptim y3
          pure (preDecs, y1 `JsSeq` y2)
      _ -> do
        app <- formApp fn argVals
        pure (preDecs, addRT rt app)

cgBody' rt (LForce (LLazyApp n args)) = cgBody rt (LApp False (LV n) args)
cgBody' rt (LLazyApp n args) =
  do
    (d,v) <- cgBody ReturnBT (LApp False (LV n) args)
    pure ([], addRT rt $ jsLazy $ jsStmt2Expr $ JsSeq (seqJs d) v)
cgBody' rt (LForce e) =
  do
    (d,v) <- cgBody GetExpBT e
    pure (d, addRT rt $ JsForce $ jsStmt2Expr v)
cgBody' rt (LLet n v sc) =
  do
    (d1, v1) <- cgBody (DecConstBT $ jsName n) v
    (d2, v2) <- cgBody rt sc
    pure $ ((d1 ++ v1 : d2), v2)
cgBody' rt (LProj e i) =
  do
    (d, v) <- cgBody GetExpBT e
    pure $ (d, addRT rt $ JsArrayProj (JsInt $ i+1) $ jsStmt2Expr v)
cgBody' rt (LCon _  conId n args) =
  do
    z <- mapM (cgBody GetExpBT) args
    con <- formCon n (map (jsStmt2Expr . snd) z)
    pure $ (concat $ map fst z, addRT rt con)
cgBody' rt (LCase _ e alts) = do
  (d, v) <- cgBody GetExpBT e
  resName <- getNewCGName
  (decSw, entry) <-
    case (all altHasNoProj alts && length alts <= 2, v) of
      (True, _) -> pure (JsEmpty, jsStmt2Expr v)
      (False, JsExprStmt (JsVar n)) -> pure (JsEmpty, jsStmt2Expr v)
      _ -> do
        swName <- getNewCGName
        pure (JsDecConst swName $ jsStmt2Expr v, JsVar swName)
  sw' <- cgIfTree rt resName entry alts
  let sw =
        case sw' of
          (Just x) -> x
          Nothing -> JsExprStmt JsNull
  case rt of
    ReturnBT -> pure (d ++ [decSw], sw)
    (DecBT nvar) -> pure (d ++ [decSw, JsDecLet nvar JsNull], sw)
    (DecConstBT nvar) -> pure (d ++ [decSw, JsDecLet nvar JsNull], sw)
    (SetBT nvar) -> pure (d ++ [decSw], sw)
    GetExpBT ->
      pure
        (d ++ [decSw, JsDecLet resName JsNull, sw], JsExprStmt $ JsVar resName)
cgBody' rt (LConst c) =
  do
     cst <- cgConst c
     pure ([], (addRT rt) $ cst)
cgBody' rt (LOp op args) =
  do
    z <- mapM (cgBody GetExpBT) args
    res <- cgOp op (map (jsStmt2Expr . snd) z)
    pure $ (concat $ map fst z, addRT rt $ res)
cgBody' rt LNothing = pure ([], addRT rt JsNull)
cgBody' rt (LError x) = pure ([], JsError $ JsStr x)
cgBody' rt x@(LForeign dres (FStr code) args ) =
  do
    z <- mapM (cgBody GetExpBT) (map snd args)
    jsArgs <- sequence $ map cgForeignArg (zip (map fst args) (map (jsStmt2Expr . snd) z))
    jsDres <- cgForeignRes dres $ JsForeign (T.pack code) jsArgs
    pure $ (concat $ map fst z, addRT rt $ jsDres)
cgBody' _ x = error $ "Instruction " ++ show x ++ " not compilable yet"

altsRT :: Text -> BodyResTarget -> BodyResTarget
altsRT rn ReturnBT = ReturnBT
altsRT rn (DecBT n) = SetBT n
altsRT rn (SetBT n) = SetBT n
altsRT rn (DecConstBT n) = SetBT n
altsRT rn GetExpBT = SetBT rn

altHasNoProj :: LAlt -> Bool
altHasNoProj (LConCase _ _ args _) = args == []
altHasNoProj _ = True

formApp :: Name -> [JsExpr] -> State CGBodyState JsExpr
formApp fn argVals = case specialCall fn of
  Just (arity, g) | arity == length argVals -> pure $ g argVals
  _ -> do
    argsFn <- getArgList fn
    fname <- cgName fn
    case argsFn of
      Nothing -> pure $ jsCurryApp fname argVals
      Just agFn -> do
        let lenAgFn = length agFn
        let lenArgs = length argVals
        case compare lenAgFn lenArgs of
          EQ -> pure $ JsApp fname argVals
          LT -> pure $ jsCurryApp (JsApp fname (take lenAgFn argVals)) (drop lenAgFn argVals)
          GT -> do
            let part = Partial fn lenArgs lenAgFn
            addPartial part
            pure $ jsAppN (jsNamePartial part) argVals

formCon :: Name -> [JsExpr] -> State CGBodyState JsExpr
formCon n args = do
  case specialCased n of
    Just (ctor, test, match) -> pure $ ctor args
    Nothing -> do
      (conId, arity) <- getConsId n
      let hc = HiddenClass n conId arity
      addHiddenClass hc
      pure $ if (arity > 0)
        then JsNew (JsVar $ jsNameHiddenClass hc) args
        else JsVar $ jsNameHiddenClass hc

formConTest :: Name -> JsExpr -> State CGBodyState JsExpr
formConTest n x = do
  case specialCased n of
    Just (ctor, test, match) -> pure $ test x
    Nothing -> do
      (conId, arity) <- getConsId n
      pure $ JsBinOp "===" (JsProp x (T.pack "type")) (JsInt conId)
      -- if (arity > 0)
      --   then pure $ JsBinOp "===" (JsProp x (T.pack "type")) (JsInt conId)
      --   else pure $ JsBinOp "===" x (JsInt conId)

formProj :: Name -> JsExpr -> Int -> JsExpr
formProj n v i =
  case specialCased n of
    Just (ctor, test, proj) -> proj v i
    Nothing -> JsProp v (dataPartName i)

smartif :: JsExpr -> JsStmt -> Maybe JsStmt -> JsStmt
smartif cond conseq (Just alt) = JsIf cond conseq (Just alt)
smartif cond conseq Nothing = conseq

formConstTest :: JsExpr -> Const -> State CGBodyState JsExpr
formConstTest scrvar t = case t of
  BI _ -> do
    t' <- cgConst t
    cgOp' PTBool (LEq (ATInt ITBig)) [scrvar, t']
  _ -> do
    t' <- cgConst t
    pure $ JsBinOp "===" scrvar t'

cgIfTree :: BodyResTarget
         -> Text
         -> JsExpr
         -> [LAlt]
         -> State CGBodyState (Maybe JsStmt)
cgIfTree _ _ _ [] = pure Nothing
cgIfTree rt resName scrvar ((LConstCase t exp):r) = do
  (d, v) <- cgBody (altsRT resName rt) exp
  alternatives <- cgIfTree rt resName scrvar r
  test <- formConstTest scrvar t
  pure $ Just $
    smartif test (JsSeq (seqJs d) v) alternatives
cgIfTree rt resName scrvar ((LDefaultCase exp):r) = do
  (d, v) <- cgBody (altsRT resName rt) exp
  pure $ Just $ JsSeq (seqJs d) v
cgIfTree rt resName scrvar ((LConCase _ n args exp):r) = do
  alternatives <- cgIfTree rt resName scrvar r
  test <- formConTest n scrvar
  st <- get
  let rwn = reWrittenNames st
  put $
    st
    { reWrittenNames =
        foldl
          (\m (n, j) -> Map.insert n (formProj n scrvar j) m)
          rwn
          (zip args [1 ..])
    }
  (d, v) <- cgBody (altsRT resName rt) exp
  st1 <- get
  put $ st1 {reWrittenNames = rwn}
  let branchBody = JsSeq (seqJs d) v
  pure $ Just $ smartif test branchBody alternatives


cgForeignArg :: (FDesc, JsExpr) -> State CGBodyState JsExpr
cgForeignArg (FApp (UN "JS_IntT") _, v) = pure v
cgForeignArg (FCon (UN "JS_Str"), v) = pure v
cgForeignArg (FCon (UN "JS_Ptr"), v) = pure v
cgForeignArg (FCon (UN "JS_Unit"), v) = pure v
cgForeignArg (FCon (UN "JS_Float"), v) = pure v
cgForeignArg (FApp (UN "JS_FnT") [_,FApp (UN "JS_Fn") [_,_, a, FApp (UN "JS_FnBase") [_,b]]], f) =
  pure f
cgForeignArg (FApp (UN "JS_FnT") [_,FApp (UN "JS_Fn") [_,_, a, FApp (UN "JS_FnIO") [_,_, b]]], f) =
  do
    jsx <- cgForeignArg (a, JsVar "x")
    jsres <- cgForeignRes b $ jsCurryApp (jsCurryApp f [jsx]) [JsNull]
    pure $ JsLambda ["x"] $ JsReturn jsres
cgForeignArg (desc, _) =
  do
    st <- get
    error $ "Foreign arg type " ++ show desc ++ " not supported. While generating function " ++ (show $ fst $ currentFnNameAndArgs st)

cgForeignRes :: FDesc -> JsExpr -> State CGBodyState JsExpr
cgForeignRes (FApp (UN "JS_IntT") _) x = pure x
cgForeignRes (FCon (UN "JS_Unit")) x = pure x
cgForeignRes (FCon (UN "JS_Str")) x = pure x
cgForeignRes (FCon (UN "JS_Ptr")) x = pure x
cgForeignRes (FCon (UN "JS_Float")) x = pure x
cgForeignRes desc val =
  do
    st <- get
    error $ "Foreign return type " ++ show desc ++ " not supported. While generating function " ++ (show $ fst $ currentFnNameAndArgs st)

setUsedITBig :: State CGBodyState ()
setUsedITBig =   modify (\s -> s {usedITBig = True})


cgConst :: Const -> State CGBodyState JsExpr
cgConst (I i) = pure $ JsInt i
cgConst (BI i) =
  do
    setUsedITBig
    pure $ JsForeign "new $JSRTS.jsbn.BigInteger(%0)" [JsStr $ show i]
cgConst (Ch c) = pure $ JsStr [c]
cgConst (Str s) = pure $ JsStr s
cgConst (Fl f) = pure $ JsDouble f
cgConst (B8 x) = pure $ JsForeign (T.pack $ show x ++ " & 0xFF") []
cgConst (B16 x) = pure $ JsForeign (T.pack $ show x ++ " & 0xFFFF") []
cgConst (B32 x) = pure $ JsForeign (T.pack $ show x ++ "|0" ) []
cgConst (B64 x) =
  do
    setUsedITBig
    pure $ JsForeign "new $JSRTS.jsbn.BigInteger(%0).and(new $JSRTS.jsbn.BigInteger(%1))" [JsStr $ show x, JsStr $ show 0xFFFFFFFFFFFFFFFF]
cgConst x | isTypeConst x = pure $ JsInt 0
cgConst x = error $ "Constant " ++ show x ++ " not compilable yet"

cgOp :: PrimFn -> [JsExpr] -> State CGBodyState JsExpr
cgOp = cgOp' PTAny

cgOp' :: JsPrimTy -> PrimFn -> [JsExpr] -> State CGBodyState JsExpr
cgOp' pt (LExternal name) _ | name == sUN "prim__null" = pure JsNull
cgOp' pt (LExternal name) [l,r] | name == sUN "prim__eqPtr" = pure $ JsBinOp "==" l r
cgOp' pt op exps = case Map.lookup op primDB of
  Just (useBigInt, pti, combinator) -> do
    when useBigInt setUsedITBig
    pure $ jsPrimCoerce pti pt $ combinator exps
  Nothing -> error ("Operator " ++ show (op, exps) ++ " not implemented")
