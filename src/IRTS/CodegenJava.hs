{-# LANGUAGE PatternGuards #-}
module IRTS.CodegenJava (codegenJava) where

import           Core.TT                   hiding (mkApp)
import           IRTS.BCImp
import           IRTS.CodegenCommon
import           IRTS.Java.ASTBuilding
import           IRTS.Java.JTypes
import           IRTS.Java.Mangling
import           IRTS.Lang
import           IRTS.Simplified
import           Paths_idris
import           Util.System

import           Control.Applicative       hiding (Const)
import           Control.Arrow
import           Control.Monad
import qualified Control.Monad.Trans       as T
import           Control.Monad.Trans.State
import           Data.Int
import           Data.List                 (foldl', intercalate, isPrefixOf,
                                            isSuffixOf)
import           Data.Maybe                (fromJust)
import qualified Data.Text                 as T
import qualified Data.Text.IO              as TIO
import qualified Data.Vector.Unboxed       as V
import           Language.Java.Parser
import           Language.Java.Pretty
import           Language.Java.Syntax      hiding (Name)
import qualified Language.Java.Syntax      as J
import           System.Directory
import           System.Exit
import           System.FilePath
import           System.IO
import           System.Process

data CodeGenerationEnv = CodeGenerationEnv { globalVariablePositions :: [(Name, Int)] }

type CodeGeneration = StateT (CodeGenerationEnv) (Either String)
type BlockResultTransformation = [BlockStmt] -> Exp -> CodeGeneration [BlockStmt]

codegenJava :: [(Name, SExp)] -> -- initialization of globals
               [(Name, SDecl)] ->
               FilePath -> -- output file name
               [String] -> -- headers
               [String] -> -- libs
               OutputType ->
               IO ()
codegenJava globalInit defs out hdrs libs exec = do
  withTempdir (takeBaseName out) $ \ tmpDir -> do
    let srcdir = tmpDir </> "src" </> "main" </> "java"
    createDirectoryIfMissing True srcdir
    let (Ident clsName) = either error id (mkClassName out)
    let outjava = srcdir </> clsName <.> "java"
    let jout = either error
                      (prettyPrint)-- flatIndent . prettyPrint)
                      (evalStateT (mkCompilationUnit globalInit defs hdrs out) (mkCodeGenEnv globalInit))
    writeFile outjava jout
    if (exec == Raw)
       then copyFile outjava (takeDirectory out </> clsName <.> "java")
       else do
         execPom <- getExecutablePom
         execPomTemplate <- TIO.readFile execPom
         let execPom = T.replace (T.pack "$MAIN-CLASS$")
                                 (T.pack clsName)
                                 (T.replace (T.pack "$ARTIFACT-NAME$")
                                            (T.pack $ takeBaseName out)
                                            (T.replace (T.pack "$DEPENDENCIES$")
                                                       (mkPomDependencies libs)
                                                       execPomTemplate
                                            )
                                 )
         TIO.writeFile (tmpDir </> "pom.xml") execPom
         mvnCmd <- getMvn
         let args = ["-f", (tmpDir </> "pom.xml")]
         (exit, mvout, err) <- readProcessWithExitCode mvnCmd (args ++ ["compile"]) ""
         when (exit /= ExitSuccess) $ error ("FAILURE: " ++ mvnCmd ++ " compile\n" ++ err ++ mvout)
         if (exec == Object)
            then do
              classFiles <-
                map (\ clsFile -> tmpDir </> "target" </> "classes" </> clsFile)
                . filter ((".class" ==) . takeExtension)
                <$> getDirectoryContents (tmpDir </> "target" </> "classes")
              mapM_ (\ clsFile -> copyFile clsFile (takeDirectory out </> takeFileName clsFile))
                    classFiles
             else do
               (exit, mvout, err) <- readProcessWithExitCode mvnCmd (args ++ ["package"]) ""
               when (exit /= ExitSuccess) (error ("FAILURE: " ++ mvnCmd ++ " package\n" ++ err ++ mvout))
               copyFile (tmpDir </> "target" </> (takeBaseName out) <.> "jar") out
               handle <- openBinaryFile out ReadMode
               contents <- TIO.hGetContents handle
               hClose handle
               handle <- openBinaryFile out WriteMode
               TIO.hPutStr handle (T.append (T.pack jarHeader) contents)
               hFlush handle
               hClose handle
               perms <- getPermissions out
               setPermissions out (setOwnerExecutable True perms)
         readProcess mvnCmd (args ++ ["clean"]) ""
         removeFile (tmpDir </> "pom.xml")

-----------------------------------------------------------------------
-- Jar and Pom infrastructure

jarHeader :: String
jarHeader =
  "#!/bin/sh\n"
  ++ "MYSELF=`which \"$0\" 2>/dev/null`\n"
  ++ "[ $? -gt 0 -a -f \"$0\" ] && MYSELF=\"./$0\"\n"
  ++ "java=java\n"
  ++ "if test -n \"$JAVA_HOME\"; then\n"
  ++ "  java=\"$JAVA_HOME/bin/java\"\n"
  ++ "fi\n"
  ++ "exec \"$java\" $java_args -jar $MYSELF \"$@\""
  ++ "exit 1\n"

mkPomDependencies :: [String] -> T.Text
mkPomDependencies deps =
  T.concat $ map (T.concat . map (T.append (T.pack "    ")) . mkDependency . T.pack) deps
  where
    mkDependency s =
      case T.splitOn (T.pack ":") s of
        [g, a, v] ->
          [ T.pack $ "<dependency>\n"
          , T.append (T.pack "  ") $ mkGroupId g
          , T.append (T.pack "  ") $ mkArtifactId a
          , T.append (T.pack "  ") $ mkVersion v
          , T.pack $ "</dependency>\n"
          ]
        _     -> []
    mkGroupId g    = T.append (T.pack $ "<groupId>")    (T.append g $ T.pack "</groupId>\n")
    mkArtifactId a = T.append (T.pack $ "<artifactId>") (T.append a $ T.pack "</artifactId>\n")
    mkVersion v    = T.append (T.pack $ "<version>")    (T.append v $ T.pack "</version>\n")

-----------------------------------------------------------------------
-- Code generation environment

mkCodeGenEnv :: [(Name, SExp)] -> CodeGenerationEnv
mkCodeGenEnv globalInit =
  CodeGenerationEnv $ zipWith (\ (name, _) pos -> (name, pos)) globalInit [0..]

flatIndent :: String -> String
flatIndent (' ' : ' ' : xs) = flatIndent xs
flatIndent (x:xs) = x:flatIndent xs
flatIndent [] = []

-----------------------------------------------------------------------
-- File structure

mkCompilationUnit :: [(Name, SExp)] -> [(Name, SDecl)] -> [String] -> FilePath -> CodeGeneration CompilationUnit
mkCompilationUnit globalInit defs hdrs out = do
  clsName <- mkClassName out
  CompilationUnit Nothing ( [ ImportDecl False idrisRts True
                            , ImportDecl True idrisForeign True
                            , ImportDecl False idrisForeignWrapper False
                            , ImportDecl False idrisPrimFn False
                            , ImportDecl False bigInteger False
                            , ImportDecl False stringBuffer False
                            , ImportDecl False runtimeException False
                            , ImportDecl False scanner False
                            , ImportDecl False arrays False
                            , ImportDecl False callable False
                            ] ++ otherHdrs
                          )
                          <$> mkTypeDecl clsName globalInit defs
  where
    idrisRts = J.Name $ map Ident ["org", "idris", "rts"]
    idrisForeign = J.Name $ map Ident ["org", "idris", "rts", "ForeignPrimitives"]
    idrisForeignWrapper = J.Name $ map Ident ["org", "idris", "rts", "ForeignWrapper"]
    idrisPrimFn = J.Name $ map Ident ["org", "idris", "rts", "PrimFn"]
    bigInteger = J.Name $ map Ident ["java", "math", "BigInteger"]
    stringBuffer = J.Name $ map Ident ["java", "lang", "StringBuffer"]
    runtimeException = J.Name $ map Ident ["java", "lang", "RuntimeException"]
    scanner = J.Name $ map Ident ["java", "util", "Scanner"]
    arrays = J.Name $ map Ident ["java", "util", "Arrays"]
    callable = J.Name $ map Ident ["java", "util", "concurrent", "Callable"]
    otherHdrs = map ( (\ name -> ImportDecl False name False)
                      . J.Name
                      . map (Ident . T.unpack)
                      . T.splitOn (T.pack ".")
                      . T.pack)
                $ filter (not . isSuffixOf ".h") hdrs

-----------------------------------------------------------------------
-- Main class

mkTypeDecl :: Ident -> [(Name, SExp)] -> [(Name, SDecl)] -> CodeGeneration [TypeDecl]
mkTypeDecl name globalInit defs =
  (\ body -> [ClassTypeDecl $ ClassDecl [ Public
                                        ,  Annotation $ SingleElementAnnotation
                                           (jName "SuppressWarnings")
                                           (EVVal . InitExp $ jString "unchecked")
                                        ]
              name
              []
              Nothing
              []
              body])
  <$> mkClassBody globalInit (map (second (prefixCallNamespaces name)) defs)

mkClassBody :: [(Name, SExp)] -> [(Name, SDecl)] -> CodeGeneration ClassBody
mkClassBody globalInit defs =
  (\ globals defs -> ClassBody . (globals++) . addMainMethod . mergeInnerClasses $ defs)
  <$> mkGlobalContext globalInit
  <*> mapM mkDecl defs

mkGlobalContext :: [(Name, SExp)] -> CodeGeneration [Decl]
mkGlobalContext [] = return []
mkGlobalContext initExps =
  (\ exps -> [ MemberDecl $ FieldDecl [Private, Static, Final]
                                      (array objectType)
                                      [ VarDecl (VarId $ globalContextID). Just . InitExp
                                        $ ArrayCreate objectType [jInt $ length initExps] 0
                                      ]
             , InitDecl True (Block $ concat exps)
             ]
  )
  <$> mapM
        (\ (name, exp) ->
          mkUpdate (Glob name) exp (\ b e -> return $ addToBlock b e)
        )
        initExps

addMainMethod :: [Decl] -> [Decl]
addMainMethod decls
  | findMain decls = mkMainMethod : decls
  | otherwise = decls
  where
    findMain ((MemberDecl (MemberClassDecl (ClassDecl _ name _ _ _ (ClassBody body)))):_)
      | name == mangle' (UN "Main") = findMainMethod body
    findMain (_:decls) = findMain decls
    findMain [] = False

    innerMainMethod = (either error id $ mangle (UN "main"))
    findMainMethod ((MemberDecl (MethodDecl _ _ _ name [] _ _)):_)
      | name == mangle' (UN "main") = True
    findMainMethod (_:decls) = findMainMethod decls
    findMainMethod [] = False

mkMainMethod :: Decl
mkMainMethod =
  simpleMethod
    [Public, Static]
    Nothing
    "main"
    [FormalParam [] (array stringType) False (VarId $ Ident "args")]
    $ Block [ BlockStmt . ExpStmt
              $ call "idris_initArgs" [ (threadType ~> "currentThread") []
                                      , jConst "args"
                                      ]
            , BlockStmt . ExpStmt $ call (mangle' (MN 0 "runMain")) []
            ]

-----------------------------------------------------------------------
-- Inner classes (idris namespaces)

mergeInnerClasses :: [Decl] -> [Decl]
mergeInnerClasses = foldl' mergeInner []
  where
    mergeInner ((decl@(MemberDecl (MemberClassDecl (ClassDecl priv name targs ext imp (ClassBody body))))):decls)
               decl'@(MemberDecl (MemberClassDecl (ClassDecl _ name' _ ext' imp' (ClassBody body'))))
      | name == name' =
        (MemberDecl $ MemberClassDecl $
                    ClassDecl priv
                              name
                              targs
                              (mplus ext ext')
                              (imp ++ imp')
                              (ClassBody $ mergeInnerClasses (body ++ body')))
        : decls
      | otherwise = decl:(mergeInner decls decl')
    mergeInner (decl:decls) decl' = decl:(mergeInner decls decl')
    mergeInner [] decl' = [decl']



mkDecl :: (Name, SDecl) -> CodeGeneration Decl
mkDecl ((NS n (ns:nss)), decl) =
  (\ name body ->
    MemberDecl $ MemberClassDecl $ ClassDecl [Public, Static] name [] Nothing [] body)
  <$> mangle (UN ns)
  <*> mkClassBody [] [(NS n nss, decl)]
mkDecl (_, SFun name params stackSize body) =
  (\ (Ident name) params paramNames methodBody ->
    simpleMethod
      [Public, Static]
      (Just objectType)
      name
      params
      ( Block $ ( declareFinalObjectArray
                    localContextID
                    (Just (arrayInitExps $ extendWithNull paramNames stackSize))
                ) : methodBody
      )
  )
  <$> mangle name
  <*> mapM mkFormalParam params
  <*> mapM (\ p -> (ExpName) <$> mangleFull p) params
  <*> mkExp body (\ block res -> return $ block ++ [jReturn res])

mkFormalParam :: Name -> CodeGeneration FormalParam
mkFormalParam name =
  (\ name -> FormalParam [Final] objectType False (VarId name))
  <$> mangle name

-----------------------------------------------------------------------
-- Expressions

-- | Compile a simple expression and use the given continuation to postprocess
-- the resulting value.
mkExp :: SExp -> BlockResultTransformation -> CodeGeneration [BlockStmt]
-- Variables
mkExp (SV var) cont = Nothing <>@! var >>= cont []

-- Applications
mkExp (SApp pushTail name args) cont = mkApp pushTail name args >>= cont []

-- Bindings
mkExp (SLet    var newExp inExp) cont = mkLet var newExp inExp cont
mkExp (SUpdate var newExp) cont = mkUpdate var newExp cont

-- Objects
mkExp (SCon conId _ args) cont = (mkIdrisObject conId args) >>= cont []

-- Case expressions
mkExp (SCase var alts) cont = mkCase True var alts cont
mkExp (SChkCase var alts) cont = mkCase False var alts cont

-- Projections
mkExp (SProj var i) cont = (mkProjection var i) >>= cont []

-- Constants
mkExp (SConst c) cont = cont [] $ mkConstant c

-- Foreign function calls
mkExp (SForeign lang resTy text params) cont =
  (mkForeign lang resTy text params) >>= cont []

-- Primitive functions
mkExp (SOp LFork [arg]) cont = (mkThread arg) >>= cont []
mkExp (SOp LPar [arg]) cont = (Nothing <>@! arg) >>= cont []
mkExp (SOp LNoOp args) cont = (Nothing <>@! (last args)) >>= cont []
mkExp (SOp op args) cont = (mkPrimitiveFunction op args) >>= cont []

-- Empty expressions
mkExp (SNothing) cont = cont [] $ Lit Null

-- Errors
mkExp (SError err) cont = mkException err

-----------------------------------------------------------------------
-- Variable access

(<>@!) :: Maybe J.Type -> LVar -> CodeGeneration Exp
(<>@!) Nothing var =
  (ArrayAccess . ((contextArray var) @!)) <$> varPos var
(<>@!) (Just castTo) var =
  (castTo <>) <$> (Nothing <>@! var)

varPos :: LVar -> CodeGeneration Int
varPos (Loc i) = return i
varPos (Glob name) = do
  positions <- globalVariablePositions <$> get
  case lookup name positions of
    (Just pos) -> return pos
    Nothing -> T.lift . Left $ "Invalid global variable id: " ++ show name

-----------------------------------------------------------------------
-- Application (wrap method calls in tail call closures)

mkApp :: Bool -> Name -> [LVar] -> CodeGeneration Exp
mkApp False name args =
  (\ methodName params ->
    (idrisClosureType ~> "unwrapTailCall") [call methodName params]
  )
  <$> mangleFull name
  <*> mapM (Nothing <>@!) args
mkApp True name args = mkMethodCallClosure name args

mkMethodCallClosure :: Name -> [LVar] -> CodeGeneration Exp
mkMethodCallClosure name args =
  (\ name args -> closure (call name args))
  <$> mangleFull name
  <*> mapM (Nothing <>@!) args

-----------------------------------------------------------------------
-- Updates (change context array) and Let bindings (Update, execute)

mkUpdate :: LVar -> SExp -> BlockResultTransformation -> CodeGeneration [BlockStmt]
mkUpdate var exp cont = do
  pos <- varPos var
  mkExp exp (\ blk rhs -> cont blk $ ((contextArray var) @! pos) @:= rhs )

mkLet :: LVar -> SExp -> SExp -> BlockResultTransformation -> CodeGeneration [BlockStmt]
mkLet var@(Loc pos) newExp inExp cont = do
  inBlk <- mkExp inExp cont
  upd <- mkUpdate var newExp (\ blk exp -> return $ addToBlock blk exp)
  return $ upd ++ inBlk
mkLet (Glob _) _ _ _ = T.lift $ Left "Cannot let bind to global variable"

-----------------------------------------------------------------------
-- Object creation

mkIdrisObject :: Int -> [LVar] -> CodeGeneration Exp
mkIdrisObject conId args =
  (\ args ->
    InstanceCreation [] (toClassType idrisObjectType) ((jInt conId):args) Nothing
  )
  <$> mapM (Nothing <>@!) args

-----------------------------------------------------------------------
-- Case expressions

mkCase :: Bool -> LVar -> [SAlt] -> BlockResultTransformation -> CodeGeneration [BlockStmt]

mkCase checked var cases cont
  | isConstCase cases = do
    defaultStmts <- mkDefaultMatch cases cont
    ifte <- mkConstMatch var defaultStmts cases cont
    return [BlockStmt ifte]
mkCase checked var cases cont =
  (\ switchExp blocks defaultStmts ->
    [BlockStmt $ Switch switchExp (blocks ++ [SwitchBlock Default defaultStmts])]
  )
  <$> mkGetConstructorId checked var
  <*> mkConsMatch var cases cont
  <*> mkDefaultMatch cases cont

isConstCase :: [SAlt] -> Bool
isConstCase ((SConstCase _ _):_) = True
isConstCase ((SDefaultCase _):cases) = isConstCase cases
isConstCase _ = False

mkDefaultMatch :: [SAlt] -> BlockResultTransformation -> CodeGeneration [BlockStmt]
mkDefaultMatch (x@(SDefaultCase branchExpression):_) cont = mkExp branchExpression cont
mkDefaultMatch (x:xs) cont = mkDefaultMatch xs cont
mkDefaultMatch [] cont = mkException "Non-exhaustive pattern"

mkMatchConstExp :: LVar -> Const -> CodeGeneration Exp
mkMatchConstExp var c
  | isPrimitive cty =
    (\ var -> (primFnType ~> opName (LEq undefined)) [var, jc] ~==~ jInt 1)
    <$> (Just cty <>@! var)
  | isArray cty =
    (\ var -> (arraysType ~> "equals") [var, jc])
    <$> (Just cty <>@! var)
  | isString cty =
    (\ var -> ((primFnType ~> opName (LStrEq)) [var, jc] ~==~ jInt 1))
    <$> (Just cty <>@! var)
  | otherwise =
    (\ var -> (var ~> "equals") [jc])
    <$> (Just cty <>@! var)
  where
    cty = constType c
    jc = mkConstant c

mkConstMatch :: LVar -> [BlockStmt] -> [SAlt] -> BlockResultTransformation -> CodeGeneration Stmt
mkConstMatch var defaultStmts ((SConstCase constant branchExpression):cases) cont =
  (\ exp block others -> IfThenElse exp (StmtBlock $ Block block) others)
  <$> mkMatchConstExp var constant
  <*> mkExp branchExpression cont
  <*> mkConstMatch var defaultStmts cases cont
mkConstMatch var defaultStmts (c:cases) cont = mkConstMatch var defaultStmts cases cont
mkConstMatch var defaultStmts [] cont = return $ StmtBlock (Block defaultStmts)

mkGetConstructorId :: Bool -> LVar -> CodeGeneration Exp
mkGetConstructorId True var =
  (\ var -> ((idrisObjectType <> var) ~> "getConstructorId") [])
  <$> (Nothing <>@! var)
mkGetConstructorId False var =
  (\ var match ->
    Cond (InstanceOf var (toRefType idrisObjectType)) match (jInt (-1))
  )
  <$> (Nothing <>@! var)
  <*> mkGetConstructorId True var

mkConsMatch :: LVar -> [SAlt] -> BlockResultTransformation -> CodeGeneration [SwitchBlock]
mkConsMatch var ((SConCase parentStackPos consIndex _ params branchExpression):cases) cont =
  (\ block others -> (SwitchBlock (SwitchCase $ jInt consIndex) block):others)
  <$> mkCaseBinding var parentStackPos params branchExpression cont
  <*> mkConsMatch var cases cont
mkConsMatch var (_:cases) cont = mkConsMatch var cases cont
mkConsMatch _ [] _ = return []

mkCaseBinding :: LVar -> Int -> [Name] -> SExp -> BlockResultTransformation -> CodeGeneration [BlockStmt]
mkCaseBinding var stackStart [] branchExpression cont = mkExp branchExpression cont
mkCaseBinding var stackStart (params) branchExpression cont = do
  deconstruction <- mkCaseBindingDeconstruction var stackStart params
  branchBlk <- mkExp branchExpression cont
  return $ deconstruction ++ branchBlk

mkCaseBindingDeconstruction :: LVar -> Int -> [Name] -> CodeGeneration [BlockStmt]
mkCaseBindingDeconstruction var stackStart members =
  mapM (\ pos -> BlockStmt . ExpStmt .
         ((contextArray var @! (stackStart + pos)) @:=)  <$> mkProjection var pos
       ) ([0..(length members - 1)])

-----------------------------------------------------------------------
-- Projection (retrieve the n-th field of an object)

mkProjection :: LVar -> Int -> CodeGeneration Exp
mkProjection var memberNr =
  (\ var -> ArrayAccess $ ((var ~> "getData") []) @! memberNr)
  <$> (Just idrisObjectType <>@! var)

-----------------------------------------------------------------------
-- Constants

mkConstantArray :: (V.Unbox a) => J.Type -> (a -> Const) -> V.Vector a -> Exp
mkConstantArray cty elemToConst elems =
  ArrayCreateInit
    cty
    0
    (ArrayInit . map (InitExp . mkConstant . elemToConst) $ V.toList elems)

mkConstant :: Const -> Exp
mkConstant c@(I        x) = constType c <> (Lit . Word $ toInteger x)
mkConstant c@(BI       x) = bigInteger (show x)
mkConstant c@(Fl       x) = constType c <> (Lit . Double $ x)
mkConstant c@(Ch       x) = constType c <> (Lit . Char $ x)
mkConstant c@(Str      x) = constType c <> (Lit . String $ x)
mkConstant c@(B8       x) = constType c <> (Lit . Word $ toInteger x)
mkConstant c@(B16      x) = constType c <> (Lit . Word $ toInteger x)
mkConstant c@(B32      x) = constType c <> (Lit . Word $ toInteger x)
mkConstant c@(B64      x) = (bigInteger (show c) ~> "longValue") []
mkConstant c@(B8V      x) = mkConstantArray (constType c) B8  x
mkConstant c@(B16V     x) = mkConstantArray (constType c) B16 x
mkConstant c@(B32V     x) = mkConstantArray (constType c) B32 x
mkConstant c@(B64V     x) = mkConstantArray (constType c) B64 x
mkConstant c@(AType    x) = ClassLit (Just $ box (constType c))
mkConstant c@(StrType   ) = ClassLit (Just $ stringType)
mkConstant c@(PtrType   ) = ClassLit (Just $ objectType)
mkConstant c@(VoidType  ) = ClassLit (Just $ voidType)
mkConstant c@(Forgot    ) = ClassLit (Just $ objectType)

-----------------------------------------------------------------------
-- Foreign function calls

mkForeignWrappedMethod :: FCallType -> FType -> String -> [(FType, LVar)] -> CodeGeneration Decl
mkForeignWrappedMethod callType resTy text params
  | callType <- FStatic      =
    (\ method args ->
      wrapperMethod $ wrapReturn resTy (call method args)
    )
    <$> liftParsed (parser name text)
    <*> foreignVarAccess params
  | callType <- FObject      =
    (\ method (tgt:args) ->
      wrapperMethod $ wrapReturn resTy ((tgt ~> (show $ pretty method)) args)
    )
    <$> liftParsed (parser ident text)
    <*> foreignVarAccess params
  | callType <- FConstructor =
    (\ clsTy args ->
      wrapperMethod $ wrapReturn resTy (InstanceCreation [] clsTy args Nothing)
    )
    <$> liftParsed (parser classType text)
    <*> foreignVarAccess params
  where
    wrapperMethod =
      MemberDecl . MethodDecl
        [Protected, Final] [] (Just objectType) (Ident $ "wrappedInvoke") [] [toRefType exceptionType]
          . MethodBody . Just . Block


    wrapReturn FUnit exp = [ BlockStmt $ ExpStmt exp, jReturn (Lit Null) ]
    wrapReturn _     exp = [ jReturn exp ]

    foreignVarAccess args =
      mapM (\ (fty, var) -> (foreignType fty <>@! var)) args

mkForeign :: FLang -> FType -> String -> [(FType, LVar)] -> CodeGeneration Exp
mkForeign (LANG_JAVA callType) resTy text params =
  (\ wrappedMethod ->
    ((InstanceCreation
       []
       (toClassType foreignWrapperType)
       []
       (Just $ ClassBody [wrappedMethod])
     ) ~> "invoke") []
  )
  <$> mkForeignWrappedMethod callType resTy text params
mkForeign (LANG_C) resTy text params = mkForeign (LANG_JAVA FStatic) resTy text params

-----------------------------------------------------------------------
-- Primitive functions

mkPrimitiveFunction :: PrimFn -> [LVar] -> CodeGeneration Exp
mkPrimitiveFunction op args =
  (\ args -> (primFnType ~> opName op) args)
  <$> sequence (zipWith (\ a t -> (Just t) <>@! a) args (sourceTypes op))

mkThread :: LVar -> CodeGeneration Exp
mkThread arg =
  (\ closure -> (closure ~> "fork") []) <$> mkMethodCallClosure (MN 0 "EVAL") [arg]

-----------------------------------------------------------------------
-- Exceptions

mkException :: String -> CodeGeneration [BlockStmt]
mkException err =
  return $
  [ BlockStmt $ Throw
      ( InstanceCreation
          []
          (toClassType runtimeExceptionType)
          [Lit $ String err]
          Nothing
      )
  ]

