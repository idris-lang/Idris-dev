{-# LANGUAGE PatternGuards #-}
module IRTS.CodegenJava (codegenJava) where

import           Idris.Core.TT             hiding (mkApp)
import           IRTS.CodegenCommon
import           IRTS.Java.ASTBuilding
import           IRTS.Java.JTypes
import           IRTS.Java.Mangling
import           IRTS.Java.Pom (pomString)
import           IRTS.Lang
import           IRTS.Simplified
import           IRTS.System
import           Util.System

import           Control.Applicative       hiding (Const)
import           Control.Arrow
import           Control.Monad
import           Control.Monad.Error
import qualified Control.Monad.Trans       as T
import           Control.Monad.Trans.State
import           Data.List                 (foldl', isSuffixOf)
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

-----------------------------------------------------------------------
-- Main function
codegenJava :: CodeGenerator
codegenJava cg = codegenJava' [] (simpleDecls cg) (outputFile cg)
                                 (includes cg) (compileLibs cg)
                                 (outputType cg)

codegenJava' :: [(Name, SExp)] -> -- initialization of globals
                [(Name, SDecl)] -> -- decls
                FilePath -> -- output file name
                [String] -> -- headers
                [String] -> -- libs
                OutputType ->
                IO ()
codegenJava' globalInit defs out hdrs libs exec =
  withTgtDir exec out (codegenJava' exec)
  where
    codegenJava' :: OutputType -> FilePath -> IO ()
    codegenJava' Raw tgtDir = do
        srcDir <- prepareSrcDir exec tgtDir
        generateJavaFile globalInit defs hdrs srcDir out
    codegenJava' MavenProject tgtDir = do
      codegenJava' Raw tgtDir
      generatePom tgtDir out libs
    codegenJava' Object tgtDir = do
      codegenJava' MavenProject tgtDir
      invokeMvn tgtDir "compile"
      copyClassFiles tgtDir out
      cleanUpTmp tgtDir
    codegenJava' _  tgtDir = do
        codegenJava' MavenProject tgtDir
        invokeMvn tgtDir "package";
        copyJar tgtDir out
        makeJarExecutable out
        cleanUpTmp tgtDir

-----------------------------------------------------------------------
-- Compiler IO

withTgtDir :: OutputType -> FilePath -> (FilePath -> IO ()) -> IO ()
withTgtDir Raw out action = action (dropFileName out)
withTgtDir MavenProject out action = createDirectoryIfMissing False out >> action out
withTgtDir _ out action = withTempdir (takeBaseName out) action

prepareSrcDir :: OutputType -> FilePath -> IO FilePath
prepareSrcDir Raw tgtDir = return tgtDir
prepareSrcDir _ tgtDir = do
  let srcDir = (tgtDir </> "src" </> "main" </> "java")
  createDirectoryIfMissing True srcDir
  return srcDir

javaFileName :: FilePath -> FilePath -> FilePath
javaFileName srcDir out =
  either error (\ (Ident clsName) -> srcDir </> clsName <.> "java") (mkClassName out)

generateJavaFile :: [(Name, SExp)] -> -- initialization of globals
                    [(Name, SDecl)] -> -- definitions
                    [String] -> -- headers
                    FilePath -> -- Source dir
                    FilePath -> -- output target
                    IO ()
generateJavaFile globalInit defs hdrs srcDir out = do
    let code = either error
                      (prettyPrint)-- flatIndent . prettyPrint)
                      (evalStateT (mkCompilationUnit globalInit defs hdrs out) mkCodeGenEnv)
    writeFile (javaFileName srcDir out) code

pomFileName :: FilePath -> FilePath
pomFileName tgtDir = tgtDir </> "pom.xml"

generatePom :: FilePath -> -- tgt dir
               FilePath -> -- output target
               [String] -> -- libs
               IO ()
generatePom tgtDir out libs = writeFile (pomFileName tgtDir) execPom
  where
    (Ident clsName) = either error id (mkClassName out)
    execPom = pomString clsName (takeBaseName out) libs
  

invokeMvn :: FilePath -> String -> IO ()
invokeMvn tgtDir command = do
   mvnCmd <- getMvn
   let args = ["-f", pomFileName tgtDir]
   (exit, mvout, err) <- readProcessWithExitCode mvnCmd (args ++ [command]) ""
   when (exit /= ExitSuccess) $
     error ("FAILURE: " ++ mvnCmd ++ " " ++ command ++ "\n" ++ err ++ mvout)

classFileDir :: FilePath -> FilePath
classFileDir tgtDir = tgtDir </> "target" </> "classes"

copyClassFiles :: FilePath -> FilePath -> IO ()
copyClassFiles tgtDir out = do
  classFiles <- map (\ clsFile -> classFileDir tgtDir </> clsFile)
                . filter ((".class" ==) . takeExtension)
                <$> getDirectoryContents (classFileDir tgtDir)
  mapM_ (\ clsFile -> copyFile clsFile (takeDirectory out </> takeFileName clsFile)) classFiles

jarFileName :: FilePath -> FilePath -> FilePath
jarFileName tgtDir out = tgtDir </> "target" </> (takeBaseName out) <.> "jar"

copyJar :: FilePath -> FilePath -> IO ()
copyJar tgtDir out =
  copyFile (jarFileName tgtDir out) out

makeJarExecutable :: FilePath -> IO ()
makeJarExecutable out = do
  handle <- openBinaryFile out ReadMode
  contents <- TIO.hGetContents handle
  hClose handle
  handle <- openBinaryFile out WriteMode
  TIO.hPutStr handle (T.append (T.pack jarHeader) contents)
  hFlush handle
  hClose handle
  perms <- getPermissions out
  setPermissions out (setOwnerExecutable True perms)

removePom :: FilePath -> IO ()
removePom tgtDir = removeFile (pomFileName tgtDir)

cleanUpTmp :: FilePath -> IO ()
cleanUpTmp tgtDir = do
  invokeMvn tgtDir "clean"
  removePom tgtDir

-----------------------------------------------------------------------
-- Jar and Pom infrastructure

jarHeader :: String
jarHeader =
  "#!/usr/bin/env sh\n"
  ++ "MYSELF=`which \"$0\" 2>/dev/null`\n"
  ++ "[ $? -gt 0 -a -f \"$0\" ] && MYSELF=\"./$0\"\n"
  ++ "java=java\n"
  ++ "if test -n \"$JAVA_HOME\"; then\n"
  ++ "  java=\"$JAVA_HOME/bin/java\"\n"
  ++ "fi\n"
  ++ "exec \"$java\" $java_args -jar $MYSELF \"$@\"\n"
  ++ "exit 1\n"

-----------------------------------------------------------------------
-- Code generation environment

data CodeGenerationEnv
  = CodeGenerationEnv
  { globalVariables :: [(Name, ArrayIndex)]
  , localVariables  :: [[(Int, Ident)]]
  , localVarCounter :: Int
  }

type CodeGeneration = StateT (CodeGenerationEnv) (Either String)

mkCodeGenEnv :: CodeGenerationEnv
mkCodeGenEnv = CodeGenerationEnv [] [] 0

varPos :: LVar -> CodeGeneration (Either ArrayIndex Ident)
varPos (Loc i) = do
  vars <- (concat . localVariables) <$> get
  case lookup i vars of
    (Just varName) -> return (Right varName)
    Nothing -> throwError $ "Invalid local variable id: " ++ show i
varPos (Glob name) = do
  vars <- globalVariables <$> get
  case lookup name vars of
    (Just varIdx) -> return (Left varIdx)
    Nothing -> throwError $ "Invalid global variable id: " ++ show name

pushScope :: CodeGeneration ()
pushScope =
  modify (\ env -> env { localVariables = []:(localVariables env) })

popScope :: CodeGeneration ()
popScope = do
  env <- get
  let lVars = tail $ localVariables env
  let vC = if null lVars then 0 else localVarCounter env
  put $ env { localVariables = tail (localVariables env)
            , localVarCounter = vC }

setVariable :: LVar -> CodeGeneration (Either ArrayIndex Ident)
setVariable (Loc i) = do
  env <- get
  let lVars = localVariables env
  let getter = localVar $ localVarCounter env
  let lVars' = ((i, getter) : head lVars) : tail lVars
  put $ env { localVariables = lVars'
            , localVarCounter = 1 + localVarCounter env}
  return (Right getter)
setVariable (Glob n) = do
  env <- get
  let gVars = globalVariables env
  let getter = globalContext @! length gVars
  let gVars' = (n, getter):gVars
  put (env { globalVariables = gVars' })
  return (Left getter)

pushParams :: [Ident] -> CodeGeneration ()
pushParams paramNames =
  let varMap = zipWith (flip (,)) paramNames [0..] in
  modify (\ env -> env { localVariables = varMap:(localVariables env)
                       , localVarCounter = (length varMap) + (localVarCounter env) })

flatIndent :: String -> String
flatIndent (' ' : ' ' : xs) = flatIndent xs
flatIndent (x:xs) = x:flatIndent xs
flatIndent [] = []

-----------------------------------------------------------------------
-- Maintaining control structures over code blocks

data BlockPostprocessor
  = BlockPostprocessor
  { ppInnerBlock :: [BlockStmt] -> Exp -> CodeGeneration [BlockStmt]
  , ppOuterBlock :: [BlockStmt] -> CodeGeneration [BlockStmt]
  }

ppExp :: BlockPostprocessor -> Exp -> CodeGeneration [BlockStmt]
ppExp pp exp = ((ppInnerBlock pp) [] exp) >>= ppOuterBlock pp

addReturn :: BlockPostprocessor
addReturn =
  BlockPostprocessor
  { ppInnerBlock = (\ block exp -> return $ block ++ [jReturn exp])
  , ppOuterBlock = return
  }

ignoreResult :: BlockPostprocessor
ignoreResult =
  BlockPostprocessor
  { ppInnerBlock = (\ block exp -> return block)
  , ppOuterBlock = return
  }

ignoreOuter :: BlockPostprocessor -> BlockPostprocessor
ignoreOuter pp = pp { ppOuterBlock = return }

throwRuntimeException :: BlockPostprocessor -> BlockPostprocessor
throwRuntimeException pp =
  pp
  { ppInnerBlock =
       (\ blk exp -> return $
         blk ++ [ BlockStmt $ Throw
                    ( InstanceCreation
                      []
                      (toClassType runtimeExceptionType)
                      [exp]
                      Nothing
                    )
                ]
       )
  }


rethrowAsRuntimeException :: BlockPostprocessor -> BlockPostprocessor
rethrowAsRuntimeException pp =
  pp
  { ppOuterBlock =
      (\ blk -> do
          ex <- ppInnerBlock (throwRuntimeException pp) [] (ExpName $ J.Name [Ident "ex"])
          ppOuterBlock pp
            $ [ BlockStmt $ Try
                  (Block blk)
                  [Catch (FormalParam [] exceptionType False (VarId (Ident "ex"))) $
                    Block ex
                  ]
                  Nothing
              ]
      )
  }

-----------------------------------------------------------------------
-- File structure

mkCompilationUnit :: [(Name, SExp)] -> [(Name, SDecl)] -> [String] -> FilePath -> CodeGeneration CompilationUnit
mkCompilationUnit globalInit defs hdrs out = do
  clsName <- mkClassName out
  CompilationUnit Nothing ( [ ImportDecl False idrisRts True
                            , ImportDecl True idrisPrelude True
                            , ImportDecl False bigInteger False
                            , ImportDecl False runtimeException False
                            , ImportDecl False byteBuffer False
                            ] ++ otherHdrs
                          )
                          <$> mkTypeDecl clsName globalInit defs
  where
    idrisRts = J.Name $ map Ident ["org", "idris", "rts"]
    idrisPrelude = J.Name $ map Ident ["org", "idris", "rts", "Prelude"]
    bigInteger = J.Name $ map Ident ["java", "math", "BigInteger"]
    runtimeException = J.Name $ map Ident ["java", "lang", "RuntimeException"]
    byteBuffer = J.Name $ map Ident ["java", "nio", "ByteBuffer"]
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
mkGlobalContext initExps = do
  pushScope
  varInit <-
    mapM (\ (name, exp) -> do
           pos <- setVariable (Glob name)
           mkUpdate ignoreResult (Glob name) exp
         ) initExps
  popScope
  return [ MemberDecl $ FieldDecl [Private, Static, Final]
                                      (array objectType)
                                      [ VarDecl (VarId $ globalContextID). Just . InitExp
                                        $ ArrayCreate objectType [jInt $ length initExps] 0
                                      ]
         , InitDecl True (Block $ concat varInit)
         ]

addMainMethod :: [Decl] -> [Decl]
addMainMethod decls
  | findMainMethod decls = mkMainMethod : decls
  | otherwise = decls
  where
    findMainMethod ((MemberDecl (MethodDecl _ _ _ name [] _ _)):_)
      | name == mangle' (sMN 0 "runMain") = True
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
              $ call "idris_initArgs" [ jConst "args" ]
            , BlockStmt . ExpStmt $ call (mangle' (sMN 0 "runMain")) []
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
mkDecl (_, SFun name params stackSize body) = do
  (Ident methodName) <- mangle name
  methodParams <- mapM mkFormalParam params
  paramNames <- mapM mangle params
  pushParams paramNames
  methodBody <- mkExp addReturn body
  popScope
  return $
    simpleMethod [Public, Static] (Just objectType) methodName methodParams
      (Block methodBody)

mkFormalParam :: Name -> CodeGeneration FormalParam
mkFormalParam name =
  (\ name -> FormalParam [Final] objectType False (VarId name))
  <$> mangle name

-----------------------------------------------------------------------
-- Expressions

-- | Compile a simple expression and use the given continuation to postprocess
-- the resulting value.
mkExp :: BlockPostprocessor -> SExp -> CodeGeneration [BlockStmt]
-- Variables
mkExp pp (SV var) =
  (Nothing <>@! var) >>= ppExp pp

-- Applications
mkExp pp (SApp pushTail name args) =
  mkApp pushTail name args >>= ppExp pp

-- Bindings
mkExp pp (SLet    var newExp inExp) =
  mkLet pp var newExp inExp
mkExp pp (SUpdate var@(Loc i) newExp) = -- can only update locals
  mkUpdate pp var newExp
mkExp pp (SUpdate var newExp) =
  mkExp pp newExp

-- Objects
mkExp pp (SCon _ conId _ args) =
  mkIdrisObject conId args >>= ppExp pp

-- Case expressions
mkExp pp (SCase up var alts) = mkCase pp True var alts
mkExp pp (SChkCase var alts) = mkCase pp False var alts

-- Projections
mkExp pp (SProj var i) =
  mkProjection var i >>= ppExp pp

-- Constants
mkExp pp (SConst c) =
  ppExp pp $ mkConstant c

-- Foreign function calls
mkExp pp (SForeign lang resTy text params) =
  mkForeign pp lang resTy text params

-- Primitive functions
mkExp pp (SOp LFork [arg]) =
  (mkThread arg) >>= ppExp pp
mkExp pp (SOp LPar [arg]) =
  (Nothing <>@! arg) >>= ppExp pp
mkExp pp (SOp LRegisterPtr [ptr, i]) =
  (Nothing <>@! ptr) >>= ppExp pp
mkExp pp (SOp LNoOp args) =
  (Nothing <>@! (last args)) >>= ppExp pp
mkExp pp (SOp LNullPtr args) =
  ppExp pp $ Lit Null
mkExp pp (SOp op args) =
  (mkPrimitiveFunction op args) >>= ppExp pp

-- Empty expressions
mkExp pp (SNothing) = ppExp pp $ Lit Null

-- Errors
mkExp pp (SError err) = ppExp (throwRuntimeException pp) (jString err)

-----------------------------------------------------------------------
-- Variable access

(<>@!) :: Maybe J.Type -> LVar -> CodeGeneration Exp
(<>@!) Nothing var =
  either ArrayAccess (\ n -> ExpName $ J.Name [n]) <$> varPos var
(<>@!) (Just castTo) var =
  (castTo <>) <$> (Nothing <>@! var)

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

mkUpdate :: BlockPostprocessor -> LVar -> SExp -> CodeGeneration [BlockStmt]
mkUpdate pp var exp =
  mkExp
    ( pp
      { ppInnerBlock =
           (\ blk rhs -> do
               pos <- setVariable var
               vExp <- Nothing <>@! var
               ppInnerBlock pp (blk ++ [pos @:= rhs]) vExp
           )
      }
    ) exp

mkLet :: BlockPostprocessor -> LVar -> SExp -> SExp -> CodeGeneration [BlockStmt]
mkLet pp var@(Loc pos) newExp inExp =
  mkUpdate (pp { ppInnerBlock =
                    (\ blk _ -> do
                        inBlk <- mkExp pp inExp
                        return (blk ++ inBlk)
                    )
               }
           ) var newExp
mkLet _ (Glob _) _ _ = T.lift $ Left "Cannot let bind to global variable"

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

mkCase :: BlockPostprocessor -> Bool -> LVar -> [SAlt] -> CodeGeneration [BlockStmt]
mkCase pp checked var cases
  | isDefaultOnlyCase cases = mkDefaultMatch pp cases
  | isConstCase cases = do
    ifte <- mkConstMatch (ignoreOuter pp) (\ pp -> mkDefaultMatch pp cases) var cases
    ppOuterBlock pp [BlockStmt ifte]
  | otherwise = do
    switchExp <- mkGetConstructorId checked var
    matchBlocks <- mkConsMatch (ignoreOuter pp) (\ pp -> mkDefaultMatch pp cases) var cases
    ppOuterBlock pp [BlockStmt $ Switch switchExp matchBlocks]

isConstCase :: [SAlt] -> Bool
isConstCase ((SConstCase _ _):_) = True
isConstCase ((SDefaultCase _):cases) = isConstCase cases
isConstCase _ = False

isDefaultOnlyCase :: [SAlt] -> Bool
isDefaultOnlyCase [SDefaultCase _] = True
isDefaultOnlyCase [] = True
isDefaultOnlyCase _ = False

mkDefaultMatch :: BlockPostprocessor -> [SAlt] -> CodeGeneration [BlockStmt]
mkDefaultMatch pp (x@(SDefaultCase branchExpression):_) =
  do pushScope
     stmt <- mkExp pp branchExpression
     popScope
     return stmt
mkDefaultMatch pp (x:xs) = mkDefaultMatch pp xs
mkDefaultMatch pp [] =
  ppExp (throwRuntimeException pp) (jString "Non-exhaustive pattern")

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

mkConstMatch :: BlockPostprocessor ->
                (BlockPostprocessor -> CodeGeneration [BlockStmt]) ->
                LVar ->
                [SAlt] ->
                CodeGeneration Stmt
mkConstMatch pp getDefaultStmts var ((SConstCase constant branchExpression):cases) = do
  matchExp <- mkMatchConstExp var constant
  pushScope
  branchBlock <- mkExp pp branchExpression
  popScope
  otherBranches <- mkConstMatch pp getDefaultStmts var cases
  return
    $ IfThenElse matchExp (StmtBlock $ Block branchBlock) otherBranches
mkConstMatch pp getDefaultStmts var (c:cases) = mkConstMatch pp getDefaultStmts var cases
mkConstMatch pp getDefaultStmts _ [] = do
  defaultBlock <- getDefaultStmts pp
  return $ StmtBlock (Block defaultBlock)

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

mkConsMatch :: BlockPostprocessor ->
               (BlockPostprocessor -> CodeGeneration [BlockStmt]) ->
               LVar ->
               [SAlt] ->
               CodeGeneration [SwitchBlock]
mkConsMatch pp getDefaultStmts var ((SConCase parentStackPos consIndex _ params branchExpression):cases) = do
  pushScope
  caseBranch <- mkCaseBinding pp var parentStackPos params branchExpression
  popScope
  otherBranches <- mkConsMatch pp getDefaultStmts var cases
  return $
    (SwitchBlock (SwitchCase $ jInt consIndex) caseBranch):otherBranches
mkConsMatch pp getDefaultStmts var (c:cases)  = mkConsMatch pp getDefaultStmts var cases
mkConsMatch pp getDefaultStmts _ [] = do
  defaultBlock <- getDefaultStmts pp
  return $
    [SwitchBlock Default defaultBlock]

mkCaseBinding :: BlockPostprocessor -> LVar -> Int -> [Name] -> SExp -> CodeGeneration [BlockStmt]
mkCaseBinding pp var stackStart params branchExpression =
  mkExp pp (toLetIn var stackStart params branchExpression)
  where
    toLetIn :: LVar -> Int -> [Name] -> SExp -> SExp
    toLetIn var stackStart members start =
      foldr
        (\ pos inExp -> SLet (Loc (stackStart + pos)) (SProj var pos) inExp)
        start
        [0.. (length members - 1)]

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
mkConstant c@(ManagedPtrType) = ClassLit (Just $ objectType)
mkConstant c@(BufferType) = ClassLit (Just $ bufferType)
mkConstant c@(VoidType  ) = ClassLit (Just $ voidType)
mkConstant c@(Forgot    ) = ClassLit (Just $ objectType)

-----------------------------------------------------------------------
-- Foreign function calls

mkForeign :: BlockPostprocessor -> FLang -> FType -> String -> [(FType, LVar)] -> CodeGeneration [BlockStmt]
mkForeign pp (LANG_C) resTy text params = mkForeign pp (LANG_JAVA FStatic) resTy text params
mkForeign pp (LANG_JAVA callType) resTy text params
  | callType <- FStatic      = do
    method <- liftParsed (parser name text)
    args <- foreignVarAccess params
    wrapReturn resTy (call method args)
  | callType <- FObject      = do
    method <- liftParsed (parser ident text)
    (tgt:args) <- foreignVarAccess params
    wrapReturn resTy ((tgt ~> (show $ pretty method)) args)
  | callType <- FConstructor = do
    clsTy <- liftParsed (parser classType text)
    args <- foreignVarAccess params
    wrapReturn resTy (InstanceCreation [] clsTy args Nothing)
  where
    foreignVarAccess args =
      mapM (\ (fty, var) -> (foreignType fty <>@! var)) args

    pp' = rethrowAsRuntimeException pp

    wrapReturn FUnit exp =
      ((ppInnerBlock pp') [BlockStmt $ ExpStmt exp] (Lit Null)) >>= ppOuterBlock pp'
    wrapReturn _     exp =
      ((ppInnerBlock pp') [] exp) >>= ppOuterBlock pp'

-----------------------------------------------------------------------
-- Primitive functions

mkPrimitiveFunction :: PrimFn -> [LVar] -> CodeGeneration Exp
mkPrimitiveFunction op args =
  (\ args -> (primFnType ~> opName op) (endiannessArguments op ++ args))
  <$> sequence (zipWith (\ a t -> (Just t) <>@! a) args (sourceTypes op))

mkThread :: LVar -> CodeGeneration Exp
mkThread arg =
  (\ closure -> (closure ~> "fork") []) <$> mkMethodCallClosure (sMN 0 "EVAL") [arg]


