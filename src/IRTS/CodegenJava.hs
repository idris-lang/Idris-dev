module IRTS.CodegenJava (codegenJava) where

import           Core.TT
import           IRTS.BCImp
import           IRTS.CodegenCommon
import           IRTS.Lang
import           IRTS.Simplified
import           Paths_idris
import           Util.System

import           Control.Applicative
import           Control.Arrow
import           Control.Monad
import qualified Control.Monad.Trans as T
import           Control.Monad.Trans.State
import           Data.Char
import           Data.Maybe (fromJust)
import           Data.List (isPrefixOf, isSuffixOf, intercalate, foldl')
import           Data.Int
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import           Language.Java.Parser
import           Language.Java.Pretty
import           Language.Java.Syntax hiding (Name)
import qualified Language.Java.Syntax as J
import           System.Directory
import           System.Exit
import           System.FilePath
import           System.IO
import           System.Process

data CodeGenerationEnv = CodeGenerationEnv { globalVariablePositions :: [(Name, Integer)] }

type CodeGeneration = StateT (CodeGenerationEnv) (Either String)

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
    let (Ident clsName) = 
          either error id (evalStateT (mkClassName out) (mkCodeGenEnv globalInit))
    let outjava = srcdir </> clsName <.> "java"
    let jout = either error
                      (flatIndent . prettyPrint)
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

mkCodeGenEnv :: [(Name, SExp)] -> CodeGenerationEnv
mkCodeGenEnv globalInit = 
  CodeGenerationEnv $ zipWith (\ (name, _) pos -> (name, pos)) globalInit [0..]

mkCompilationUnit :: [(Name, SExp)] -> [(Name, SDecl)] -> [String] -> FilePath -> CodeGeneration CompilationUnit
mkCompilationUnit globalInit defs hdrs out =
  CompilationUnit Nothing ( [ ImportDecl False idrisRts True
                            , ImportDecl True idrisForeign True
                            , ImportDecl False bigInteger False
                            , ImportDecl False stringBuffer False
                            , ImportDecl False runtimeException False
                            , ImportDecl False scanner False
                            , ImportDecl False arrays False
                            ] ++ otherHdrs
                          )
                          <$> mkTypeDecl globalInit defs out
  where
    idrisRts = J.Name $ map Ident ["org", "idris", "rts"]
    idrisForeign = J.Name $ map Ident ["org", "idris", "rts", "ForeignPrimitives"]
    bigInteger = J.Name $ map Ident ["java", "math", "BigInteger"]
    stringBuffer = J.Name $ map Ident ["java", "lang", "StringBuffer"]
    runtimeException = J.Name $ map Ident ["java", "lang", "RuntimeException"]
    scanner = J.Name $ map Ident ["java", "util", "Scanner"]
    arrays = J.Name $ map Ident ["java", "util", "Arrays"]
    otherHdrs = map ( (\ name -> ImportDecl False name False)
                      . J.Name 
                      . map (Ident . T.unpack) 
                      . T.splitOn (T.pack ".") 
                      . T.pack) 
                $ filter (not . isSuffixOf ".h") hdrs

flatIndent :: String -> String
flatIndent (' ' : ' ' : xs) = flatIndent xs
flatIndent (x:xs) = x:flatIndent xs
flatIndent [] = []

prefixCallNamespaces :: Ident -> SExp -> SExp
prefixCallNamespaces (Ident name) (SApp tail (NS n ns) args) = SApp tail (NS n (name:ns)) args
prefixCallNamespaces name (SLet var e1 e2) = SLet var (prefixCallNamespaces name e1) (prefixCallNamespaces name e2)
prefixCallNamespaces name (SUpdate var e) = SUpdate var (prefixCallNamespaces name e)
prefixCallNamespaces name (SCase var alts) = SCase var (map (prefixCallNamespacesCase name) alts)
prefixCallNamespaces name (SChkCase var alts) = SChkCase var (map (prefixCallNamespacesCase name) alts)
prefixCallNamespaces _ exp = exp

prefixCallNamespacesCase :: Ident -> SAlt -> SAlt
prefixCallNamespacesCase name (SConCase x y n ns e) = SConCase x y n ns (prefixCallNamespaces name e)
prefixCallNamespacesCase name (SConstCase c e) = SConstCase c (prefixCallNamespaces name e)
prefixCallNamespacesCase name (SDefaultCase e) = SDefaultCase (prefixCallNamespaces name e)

prefixCallNamespacesDecl :: Ident -> SDecl -> SDecl
prefixCallNamespacesDecl name (SFun fname args i e) = SFun fname args i (prefixCallNamespaces name e)

mkTypeDecl :: [(Name, SExp)] -> [(Name, SDecl)] -> FilePath -> CodeGeneration [TypeDecl]
mkTypeDecl globalInit defs out =
  (\ name body -> [ClassTypeDecl $ ClassDecl [ Public
                                             ,  Annotation $ SingleElementAnnotation 
                                                             (J.Name [Ident "SuppressWarnings"])
                                                             (EVVal . InitExp . Lit $ String "unchecked")
                                             ] 
                                             name 
                                             [] 
                                             Nothing 
                                             [] 
                                             body])
  <$> mkClassName out
  <*> ( mkClassName out 
        >>= (\ ident -> mkClassBody globalInit (map (second (prefixCallNamespacesDecl ident)) defs))
      )

mkClassName :: FilePath -> CodeGeneration Ident
mkClassName path =
  T.lift $ left (\ err -> "Parser error in \"" ++ path ++ "\": " ++ (show err))
                (parser ident . takeBaseName $ takeFileName path)

mkClassBody :: [(Name, SExp)] -> [(Name, SDecl)] -> CodeGeneration ClassBody
mkClassBody globalInit defs = 
  (\ globals defs -> ClassBody . (globals++) . addMainMethod . mergeInnerClasses $ defs)
  <$> mkGlobalContext globalInit
  <*> mapM mkDecl defs

mkGlobalContext :: [(Name, SExp)] -> CodeGeneration [Decl]
mkGlobalContext [] = return []
mkGlobalContext initExps = 
  (\ exps -> [ MemberDecl $ FieldDecl [Private, Static, Final] 
                                      objectArrayType 
                                      [VarDecl (VarId $ Ident "globalContext") 
                                               (Just . InitArray $ ArrayInit exps)               
                                      ]
             ]
  )
  <$> mapM (\ (_, exp) -> InitExp <$> mkExp exp) initExps

  

addMainMethod :: [Decl] -> [Decl]
addMainMethod decls
  | findMain decls = mkMainMethod : decls
  | otherwise = decls
  where
    findMain ((MemberDecl (MemberClassDecl (ClassDecl _ (Ident "Main") _ _ _ (ClassBody body)))):_) =
      findMainMethod body
    findMain (_:decls) = findMain decls
    findMain [] = False

    findMainMethod ((MemberDecl (MethodDecl _ _ _ (Ident "main") [] _ _)):_) = True
    findMainMethod (_:decls) = findMainMethod decls
    findMainMethod [] = False

mkMainMethod :: Decl
mkMainMethod = 
  MemberDecl $ MethodDecl [Public, Static] 
                          [] 
                          Nothing 
                          (Ident "main") 
                          [FormalParam [] stringArrayType False (VarId $ Ident "args")]
                          [] 
                          (MethodBody . Just $ Block [ BlockStmt . ExpStmt . MethodInv $
                                                                 MethodCall (J.Name [Ident "idris_initArgs"])
                                                                            [ MethodInv $ TypeMethodCall
                                                                                        (J.Name [Ident "Thread"])
                                                                                        []
                                                                                        (Ident "currentThread")
                                                                                        []
                                                                            , ExpName $ J.Name [Ident "args"]
                                                                            ]           
                                                     , BlockStmt . ExpStmt . MethodInv $
                                                                 MethodCall (J.Name [Ident "runMain_0"])
                                                                            []
                                                     ]
                          )

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


mkIdentifier :: Name -> CodeGeneration Ident
mkIdentifier (NS name _) = mkIdentifier name
mkIdentifier (MN i name) = (\ (Ident x) -> Ident $ x ++ ('_' : show i))
                           <$> mkIdentifier (UN name)
mkIdentifier (UN name) =
  T.lift $ left (\ err -> "Parser error in \"" ++ name ++ "\": " ++ (show err))
                ( parser ident
                . cleanReserved
                . cleanNonLetter
                . cleanStart
                $ cleanWs False name)
  where
    cleanStart (x:xs)
      | isNumber x = '_' : (x:xs)
      | otherwise = (x:xs)
    cleanStart [] = []
    cleanNonLetter (x:xs)
      | x == '#' = "_Hash" ++ cleanNonLetter xs
      | x == '@' = "_At" ++ cleanNonLetter xs
      | x == '$' = "_Dollar" ++ cleanNonLetter xs
      | x == '!' = "_Bang" ++ cleanNonLetter xs
      | x == '.' = "_Dot" ++ cleanNonLetter xs
      | x == '\'' = "_Prime" ++ cleanNonLetter xs
      | x == '*' = "_Times" ++ cleanNonLetter xs
      | x == '+' = "_Plus" ++ cleanNonLetter xs
      | x == '/' = "_Divide" ++ cleanNonLetter xs
      | x == '-' = "_Minus" ++ cleanNonLetter xs
      | x == '%' = "_Mod" ++ cleanNonLetter xs
      | x == '<' = "_LessThan" ++ cleanNonLetter xs
      | x == '=' = "_Equals" ++ cleanNonLetter xs
      | x == '>' = "_MoreThan" ++ cleanNonLetter xs
      | x == '[' = "_LSBrace" ++ cleanNonLetter xs
      | x == ']' = "_RSBrace" ++ cleanNonLetter xs
      | x == '(' = "_LBrace" ++ cleanNonLetter xs
      | x == ')' = "_RBrace" ++ cleanNonLetter xs
      | x == '_' = "__" ++ cleanNonLetter xs
      | not (isAlphaNum x) = "_" ++ (show $ ord x) ++ xs
      | otherwise = x:cleanNonLetter xs
    cleanNonLetter [] = []
    cleanWs capitalize (x:xs)
      | isSpace x  = cleanWs True xs
      | capitalize = (toUpper x) : (cleanWs False xs)
      | otherwise  = x : (cleanWs False xs)
    cleanWs _ [] = []


    cleanReserved "param" = "_param"
    cleanReserved "globalContext" = "_globalContext"
    cleanReserved "context" = "_context"
    cleanReserved "newcontext" = "_newcontext"

    cleanReserved "void" = "_void"
    cleanReserved "null" = "_null"
    cleanReserved "int" = "_int"
    cleanReserved "long" = "_long"
    cleanReserved "char" = "_char"
    cleanReserved "byte" = "_byte"
    cleanReserved "double" = "_double"
    cleanReserved "float" = "_float"
    cleanReserved "boolean" = "_boolean"
    cleanReserved "Object" = "_Object"
    cleanReserved "String" = "_String"
    cleanReserved "StringBuilder" = "_StringBuilder"
    cleanReserved "StringBuffer" = "_StringBuffer"
    cleanReserved "Scanner" = "_Scanner"
    cleanReserved "Integer" = "_Integer"
    cleanReserved "Double" = "_Double"
    cleanReserved "Byte" = "_Byte"
    cleanReserved "Character" = "_Character"
    cleanReserved "BigInteger" = "_BigInteger"
    cleanReserved "Boolean" = "_Boolean"
    cleanReserved "Closure" = "_Closure"
    cleanReserved "IdrisObject" = "_IdrisObject"
    cleanReserved "TailCallClosure" = "_TailCallClosure"
    cleanReserved "System" = "_System"
    cleanReserved "Math" = "_Math"
    cleanReserved "Arrays" = "_Arrays"
    cleanReserved "RuntimeException" = "_RuntimeException"
    cleanReserved "Comparable" = "_Comparable"

    cleanReserved "class" = "_class"
    cleanReserved "enum" = "_enum"
    cleanReserved "interface" = "_interface"
    cleanReserved "extends" = "_extends"
    cleanReserved "implements" = "_implements"
    cleanReserved "public" = "_public"
    cleanReserved "private" = "_private"
    cleanReserved "protected" = "_protected"
    cleanReserved "static" = "_static"
    cleanReserved "final" = "_final"
    cleanReserved "abstract" = "_abstract"
    cleanReserved "strict" = "_strict"
    cleanReserved "volatile" = "_volatile"
    cleanReserved "transient" = "_transient"
    cleanReserved "native" = "_native"
    cleanReserved "const" = "_const"

    cleanReserved "import" = "_import"
    cleanReserved "package" = "_package"

    cleanReserved "throw" = "_throw"
    cleanReserved "throws" = "_throws"
    cleanReserved "try" = "_try"
    cleanReserved "catch" = "_catch"

    cleanReserved "synchronized" = "_synchronized"

    cleanReserved "if" = "_if"
    cleanReserved "else" = "_else"
    cleanReserved "switch" = "_switch"
    cleanReserved "case" = "_case"
    cleanReserved "default" = "_default"

    cleanReserved "while" = "_while"
    cleanReserved "for" = "_for"
    cleanReserved "do" = "_do"
    cleanReserved "break" = "_break"
    cleanReserved "continue" = "_continue"
    cleanReserved "goto" = "_goto"

    cleanReserved "this" = "_this"
    cleanReserved "super" = "_super"
    cleanReserved "new" = "_new"
    cleanReserved "return" = "_return"

    cleanReserved "idris_initArgs" = "_idris_initArgs"
    cleanReserved "idris_numArgs" = "_idris_numArgs"
    cleanReserved "idris_getArg" = "_idris_getArg"
    cleanReserved "getenv" = "_getenv"
    cleanReserved "exit" = "_exit"
    cleanReserved "usleep" = "_usleep"
    cleanReserved "idris_sendMessage" = "_idris_sendMessage"
    cleanReserved "idris_checkMessage" = "_idris_checkMessage"
    cleanReserved "idris_recvMessage" = "_idris_recvMessage"
    cleanReserved "putStr" = "_putStr"
    cleanReserved "putchar" = "_putchar"
    cleanReserved "getchar" = "_getchar"
    cleanReserved "fileOpen" = "_fileOpen"
    cleanReserved "fileClose" = "_fileClose"
    cleanReserved "fputStr" = "_fputStr"
    cleanReserved "fileEOF" = "_fileEOF"
    cleanReserved "isNull" = "_isNull"
    cleanReserved "idris_K" = "_idris_K"
    cleanReserved "idris_flipK" = "_idris_flipK"
    cleanReserved "idris_assignStack" = "_idris_assignStack"
    cleanReserved "free" = "_free"
    cleanReserved "malloc" = "_malloc"
    cleanReserved "idris_memset" = "_idris_memset"
    cleanReserved "idris_peek" = "_idris_peek"
    cleanReserved "idris_poke" = "_idris_poke"
    cleanReserved "idris_memmove" = "_idris_memmove"

    cleanReserved x = x

mkName :: Name -> CodeGeneration J.Name
mkName (NS name nss) = (\ n ns -> J.Name (n:ns))
                       <$> mkIdentifier name
                       <*> mapM (mkIdentifier . UN) nss
mkName n = J.Name . (:[]) <$> mkIdentifier n

voidType :: ClassType
voidType = ClassType [(Ident "Void", [])]

objectType :: ClassType
objectType = ClassType [(Ident "Object", [])]

objectArrayType :: Language.Java.Syntax.Type
objectArrayType = RefType . ArrayType . RefType . ClassRefType $ objectType

idrisClosureType :: ClassType
idrisClosureType = ClassType [(Ident "Closure", [])]

idrisTailCallClosureType :: ClassType
idrisTailCallClosureType = ClassType [(Ident "TailCallClosure", [])]

idrisObjectType :: ClassType
idrisObjectType = ClassType [(Ident "IdrisObject", [])]

contextArray :: LVar -> Exp
contextArray (Loc _) = ExpName $ J.Name [Ident "context"]
contextArray (Glob _) = ExpName $ J.Name [Ident "globalContext"]

charType :: ClassType
charType = ClassType [(Ident "Character", [])]

byteType :: ClassType
byteType = ClassType [(Ident "Byte", [])]

shortType :: ClassType
shortType = ClassType [(Ident "Short", [])]

integerType :: ClassType
integerType = ClassType [(Ident "Integer", [])]

longType :: ClassType
longType = ClassType [(Ident "Long", [])]

nextIntTy :: IntTy -> IntTy
nextIntTy (ITFixed IT8) = (ITFixed IT16)
nextIntTy (ITFixed IT16) = (ITFixed IT32)
nextIntTy (ITFixed IT32) = (ITFixed IT64)
nextIntTy (ITFixed IT64) = (ITFixed IT64)
nextIntTy ITNative = (ITFixed IT64)

intTyToIdent :: IntTy -> Ident
intTyToIdent (ITFixed IT8)  = Ident "Byte"
intTyToIdent (ITFixed IT16) = Ident "Short"
intTyToIdent (ITFixed IT32) = Ident "Integer"
intTyToIdent (ITFixed IT64) = Ident "Long"
intTyToIdent ITNative = Ident "Integer"
intTyToIdent ITBig = Ident "BigInteger"

intTyToClass :: IntTy -> ClassType
intTyToClass ty = ClassType [(intTyToIdent ty, [])]

intTyToMethod :: IntTy -> String
intTyToMethod (ITFixed IT8)  = "byteValue"
intTyToMethod (ITFixed IT16) = "shortValue"
intTyToMethod (ITFixed IT32) = "intValue"
intTyToMethod (ITFixed IT64) = "longValue"
intTyToMethod ITNative = "intValue"

intTyToPrimTy :: IntTy -> PrimType
intTyToPrimTy (ITFixed IT8)  = ByteT
intTyToPrimTy (ITFixed IT16) = ShortT
intTyToPrimTy (ITFixed IT32) = IntT
intTyToPrimTy (ITFixed IT64) = LongT
intTyToPrimTy ITNative = IntT

bigIntegerType :: ClassType
bigIntegerType = ClassType [(Ident "BigInteger", [])]

doubleType :: ClassType
doubleType = ClassType [(Ident "Double", [])]

stringType :: ClassType
stringType = ClassType [(Ident "String", [])]

stringArrayType :: Language.Java.Syntax.Type
stringArrayType = RefType . ArrayType . RefType . ClassRefType $ stringType

exceptionType :: ClassType
exceptionType = ClassType [(Ident "Throwable", [])]

runtimeExceptionType :: ClassType
runtimeExceptionType = ClassType [(Ident "RuntimeException", [])]

comparableType :: ClassType
comparableType = ClassType [(Ident "Comparable", [])]

mkDecl :: (Name, SDecl) -> CodeGeneration Decl
mkDecl ((NS n (ns:nss)), decl) =
  (\ name body -> MemberDecl $ MemberClassDecl $ ClassDecl [Public, Static] name [] Nothing [] body)
  <$> mkIdentifier (UN ns)
  <*> mkClassBody [] [(NS n nss, decl)]
mkDecl (_, SFun name params stackSize body) =
  (\ name params paramNames methodBody ->
     MemberDecl $ MethodDecl [Public, Static]
                             []
                             (Just . RefType $ ClassRefType objectType)
                             name
                             params
                             []
                             (MethodBody . Just $ Block 
                                           [ LocalVars [Final]
                                                       objectArrayType
                                                       [ VarDecl (VarDeclArray . VarId $ Ident "context")
                                                                 (Just . InitArray . ArrayInit $
                                                                       paramNames 
                                                                       ++ replicate stackSize (InitExp . Lit $ Null))
                                                       ]
                                           , BlockStmt . Return $ Just methodBody
                                           ]
                             )
  )
  <$> mkIdentifier name
  <*> mapM mkFormalParam params
  <*> mapM (\ p -> (InitExp . ExpName) <$> mkName p) params
  <*> mkExp body


mkClosure :: [Name] -> Int -> SExp -> CodeGeneration Exp
mkClosure params stackSize body =
  (\ paramArray body -> 
     InstanceCreation [] 
                      idrisClosureType 
                      [paramArray]
                      (Just $ ClassBody [body])
  )
  <$> mkStackInit params stackSize
  <*> mkClosureCall body

mkFormalParam :: Name -> CodeGeneration FormalParam
mkFormalParam name =
  (\ name -> FormalParam [Final] (RefType . ClassRefType $ objectType) False (VarId name))
  <$> mkIdentifier name

mkClosureCall :: SExp -> CodeGeneration Decl
mkClosureCall body =
  (\ body -> MemberDecl $ MethodDecl [Public] [] (Just . RefType $ ClassRefType objectType) (Ident "call") [] [] body)
  <$> mkMethodBody body

mkMethodBody :: SExp -> CodeGeneration MethodBody
mkMethodBody exp =
  (\ exp -> MethodBody . Just . Block $ [BlockStmt . Return . Just $ exp])
  <$> mkExp exp

mkStackInit :: [Name] -> Int -> CodeGeneration Exp
mkStackInit params stackSize =
  (\ localVars -> ArrayCreateInit objectArrayType 0 . ArrayInit $
                  (map (InitExp . ExpName) localVars)
                  ++ (replicate (stackSize) (InitExp $ Lit Null)))
  <$> mapM mkName params

mkK :: Exp -> Exp -> Exp
mkK result drop = 
  MethodInv $ MethodCall (J.Name [Ident "idris_K"]) [ result, drop ]

mkFlipK :: Exp -> Exp -> Exp
mkFlipK drop result = 
  MethodInv $ MethodCall (J.Name [Ident "idris_flipK"]) [ drop, result ]

mkLet :: LVar -> SExp -> SExp -> CodeGeneration Exp
mkLet (Loc pos) oldExp newExp =
  (\ oldExp newExp ->
     mkFlipK ( Assign ( ArrayLhs $ ArrayIndex (ExpName $ J.Name [Ident "context"])
                                              (Lit $ Int (toInteger pos)))
                      EqualA
                      newExp
             )
             oldExp
  )
  <$> mkExp oldExp
  <*> mkExp newExp
mkLet (Glob _) _ _ = T.lift $ Left "Cannot let bind to global variable"

reverseNameSpace :: J.Name -> J.Name
reverseNameSpace (J.Name ids) =
  J.Name ((tail ids) ++ [head ids])

mkCase :: Bool -> LVar -> [SAlt] -> CodeGeneration Exp
mkCase checked var ((SConCase parentStackPos consIndex _ params branchExpression):cases) =
  mkConsCase checked
             var
             parentStackPos 
             consIndex 
             params 
             branchExpression
             (SCase var cases)
mkCase checked var (c@(SConstCase constant branchExpression):cases) =
  (\ constant branchExpression alternative var-> 
     Cond ( MethodInv $ PrimaryMethodCall (constant)
                                          []
                                          (Ident "equals")
                                          [var]
          )
          branchExpression
          alternative
  )
  <$> mkExp (SConst constant)
  <*> mkExp branchExpression
  <*> mkCase checked var cases
  <*> mkVarAccess Nothing var
mkCase checked var (SDefaultCase exp:cases) = mkExp exp
mkCase checked  _ [] = mkExp (SError "Non-exhaustive pattern")

mkConsCase :: Bool -> LVar -> Int -> Int -> [Name] -> SExp -> SExp -> CodeGeneration Exp
mkConsCase checked
           toDeconstruct
           parentStackStart 
           consIndex 
           params 
           branchExpression 
           alternative =
  (\ caseBinding alternative var varCasted-> 
     Cond (BinOp (InstanceOf (var) 
                             (ClassRefType idrisObjectType)
                 )
                 CAnd
                 ( BinOp
                   ( MethodInv $ PrimaryMethodCall (varCasted)
                                                   []
                                                   (Ident "getConstructorId")
                                                   []
                   )
                   Equal
                   (Lit $ Int (toInteger consIndex))
                 )
          )
          (caseBinding)
          alternative
  )
  <$> mkCaseBinding checked toDeconstruct parentStackStart params branchExpression
  <*> mkExp alternative
  <*> mkVarAccess (Nothing) toDeconstruct
  <*> mkVarAccess (Just idrisObjectType) toDeconstruct


mkCaseBinding :: Bool -> LVar -> Int -> [Name] -> SExp -> CodeGeneration Exp
mkCaseBinding True  var parentStackStart params branchExpression =
  (\ branchExpression deconstruction -> 
     mkFlipK (MethodInv $ MethodCall (J.Name [Ident "idris_assignStack"])
             ( (ExpName $ J.Name [Ident "context"])
               : (Lit $ Int (toInteger parentStackStart))
               : deconstruction
             ))
             (branchExpression)
  )
  <$> mkExp branchExpression
  <*> mkCaseBindingDeconstruction var params
mkCaseBinding False var parentStackStart params branchExpression =
  (\ bindingMethod deconstruction ->
     MethodInv $ PrimaryMethodCall 
               ( MethodInv $ PrimaryMethodCall (InstanceCreation []
                                                                 (ClassType [(Ident "Object", [])])
                                                                 []
                                                                 (Just $ ClassBody [MemberDecl $ bindingMethod])
                                               )
                                               []
                                               (Ident "apply")
                                               ( contextArray (Loc undefined) : deconstruction )
               )
               []
               (Ident "call")
               []
  )
  <$> mkCaseBindingMethod parentStackStart params branchExpression
  <*> mkCaseBindingDeconstruction var params

mkCaseBindingDeconstruction :: LVar -> [Name] -> CodeGeneration [Exp]
mkCaseBindingDeconstruction var members =
  mapM (mkProjection var) ([0..(length members - 1)])

mkCaseBindingMethod :: Int -> [Name] -> SExp -> CodeGeneration MemberDecl
mkCaseBindingMethod parentStackStart params branchExpression =
  (\ formalParams caseBindingStack branchExpression -> 
     MethodDecl [Final, Public]
                []
                (Just . RefType $ ClassRefType idrisClosureType)
                (Ident "apply")
                (mkContextParam:formalParams)
                []
                (MethodBody . Just . Block $
                              caseBindingStack ++
                              [BlockStmt . Return $ Just branchExpression]))
  <$> mapM mkFormalParam params
  <*> mkBindingStack False parentStackStart params
  <*> mkBindingClosure branchExpression

mkContextParam :: FormalParam
mkContextParam = 
  FormalParam [Final] (objectArrayType) False (VarId (Ident "context"))

mkBindingClosure :: SExp -> CodeGeneration Exp
mkBindingClosure oldExp =
  (\ oldCall -> 
     InstanceCreation [] 
                      idrisClosureType
                      [ ExpName $ J.Name [Ident "new_context"] ]
                      (Just $ ClassBody [oldCall])
  )
  <$> mkClosureCall oldExp


mkBindingStack :: Bool -> Int -> [Name] -> CodeGeneration [BlockStmt]
mkBindingStack checked parentStackStart params =
  (\ paramNames ->
    ( LocalVars [Final]
                objectArrayType
                [ VarDecl (VarDeclArray . VarId $ Ident "new_context")
                          (Just . InitExp $ mkContextCopy checked parentStackStart params)
                ])
    : ( map (\ (param, pos) ->
               BlockStmt . ExpStmt $
                         Assign (ArrayLhs $ ArrayIndex (ExpName $ J.Name [Ident "new_context"])
                                                       (Lit $ Int (toInteger pos)))
                                EqualA
                                (ExpName param)) $ zip paramNames [parentStackStart..]
      )
  ) 
  <$> mapM mkName params

mkContextCopy :: Bool -> Int -> [Name] -> Exp
mkContextCopy True parentStackStart params =
  MethodInv $ PrimaryMethodCall (ExpName $ J.Name [Ident "context"])
                                []
                                (Ident "clone")
                                []
mkContextCopy False parentStackStart params =
  MethodInv $ TypeMethodCall (J.Name [Ident "Arrays"])
                             []
                             (Ident "copyOf")
                             [ ExpName $ J.Name [Ident "context"]
                             , MethodInv
                             $ TypeMethodCall (J.Name [Ident "Math"])
                                 []
                                 (Ident "max")
                                 [ FieldAccess $ PrimaryFieldAccess (ExpName $ J.Name [Ident "context"])
                                                                    (Ident "length")
                                 , Lit . Int $ toInteger (parentStackStart + length params)
                                 ]
                             ]

mkProjection :: LVar -> Int -> CodeGeneration Exp
mkProjection var memberNr =
  (\ var -> ArrayAccess $ ArrayIndex ( MethodInv $ PrimaryMethodCall
                                                   (var)
                                                   []
                                                   (Ident "getData")
                                                   []
                                     )
                                     (Lit $ Int (toInteger memberNr))
  )
  <$> mkVarAccess (Just idrisObjectType) var

type ClassName = String

mkPrimitive :: ClassName -> Literal -> Exp
mkPrimitive className value = 
  MethodInv $ TypeMethodCall (J.Name [Ident className]) 
                             []
                             (Ident "valueOf")
                             [Lit $ value]

mkClass :: ClassType -> Exp
mkClass classType =
  ClassLit . Just . RefType .ClassRefType $ classType

mkBinOpExp :: ClassType -> Op -> [LVar] -> CodeGeneration Exp
mkBinOpExp castTo op (var:vars) = do
  start <- mkVarAccess (Just castTo) var
  foldM (\ exp var -> BinOp exp op <$> mkVarAccess (Just castTo) var) start vars

mkBinOpExpTrans :: (Exp -> Exp) -> (Exp -> Exp) -> ClassType -> Op -> [LVar] -> CodeGeneration Exp
mkBinOpExpTrans opTransformation resultTransformation castTo op (var:vars) = do
  start <- (mkVarAccess (Just castTo) var) 
  foldM (\ exp var -> resultTransformation 
                        . BinOp (opTransformation exp) op 
                        . opTransformation 
                        <$> mkVarAccess (Just castTo) var) 
        start
        vars

mkBinOpExpConv :: String -> PrimType -> ClassType -> Op -> [LVar] -> CodeGeneration Exp
mkBinOpExpConv fromMethodName toType fromType@(ClassType [(cls@(Ident _), [])]) op args =
  mkBinOpExpTrans (\ exp -> MethodInv $ TypeMethodCall (J.Name [cls]) 
                                                       [] 
                                                       (Ident fromMethodName) 
                                                       [exp]
                  ) 
                  (\ exp -> MethodInv $ TypeMethodCall (J.Name [cls]) 
                                                       [] 
                                                       (Ident "valueOf") 
                                                       [Cast (PrimType $ toType) exp]
                  )
                  fromType
                  op 
                  args

mkLogicalBinOpExp :: ClassType -> Op -> [LVar] -> CodeGeneration Exp
mkLogicalBinOpExp castTo op (var:vars) = do
  start <- mkVarAccess (Just castTo) var
  foldM (\ exp var -> mkBoolToNumber castTo . BinOp exp op <$> mkVarAccess (Just castTo) var) 
        start
        vars

mkMethodOpChain1 :: (Exp -> Exp) -> ClassType -> String -> [LVar] -> CodeGeneration Exp
mkMethodOpChain1 = mkMethodOpChain id

mkMethodOpChain :: (Exp -> Exp) -> (Exp -> Exp) -> ClassType -> String -> [LVar] -> CodeGeneration Exp
mkMethodOpChain initialTransformation resultTransformation castTo method (arg:args) = do
  start <- initialTransformation <$> mkVarAccess (Just $ castTo) arg
  foldM (\ exp arg' -> 
           resultTransformation 
           . MethodInv 
           . PrimaryMethodCall exp [] (Ident method)
           . (:[])
           <$> mkVarAccess (Just $ castTo) arg'
        )
        start
        args

mkBoolToNumber :: ClassType -> Exp -> Exp
mkBoolToNumber (ClassType [(Ident name, [])]) boolExp =
  Cond boolExp (mkPrimitive name (Int 1)) (mkPrimitive name (Int 0))

mkZeroExt :: String -> Int -> ClassType -> ClassType -> LVar -> CodeGeneration Exp
mkZeroExt toMethod bits fromType toType@(ClassType [(toTypeName, [])]) var = do
  (\ var sext -> 
     MethodInv $ TypeMethodCall (J.Name [toTypeName])
                                []
                                (Ident "valueOf")
                                [ Cond ( BinOp (var)
                                               LThan
                                               (Lit $ Int 0)
                                       )
                                       ( BinOp (Lit $ Int (2^bits))
                                               Add
                                               (sext)
                                       )
                                       sext
                                ]
   )
  <$> mkVarAccess (Just $ fromType) var
  <*> mkSignedExt' toMethod fromType var
  
mkSignedExt :: String -> ClassType -> ClassType -> LVar -> CodeGeneration Exp
mkSignedExt toMethod fromType (ClassType [(toTypeName, [])]) var =
  (\ sext -> MethodInv $ TypeMethodCall (J.Name [toTypeName])
                                        []
                                        (Ident "valueOf")
                                        [ sext ]
  )
  <$> mkSignedExt' toMethod fromType var

mkSignedExt' :: String -> ClassType -> LVar -> CodeGeneration Exp
mkSignedExt' toMethod fromType var =
  (\ var -> MethodInv $ PrimaryMethodCall (var)
                                          [] 
                                          (Ident toMethod)
                                          []
  )
  <$> mkVarAccess (Just $ fromType) var

data SPartialOrder
  = SLt
  | SLe
  | SEq
  | SGe
  | SGt

mkPartialOrder :: SPartialOrder -> Exp -> Exp
mkPartialOrder SLt x = (BinOp (Lit $ Int (-1)) Equal x)
mkPartialOrder SLe x = 
  BinOp (BinOp (Lit $ Int (-1)) Equal x)
        COr
        (BinOp (Lit $ Int 0) Equal x)
mkPartialOrder SEq x = BinOp (Lit $ Int 0) Equal x
mkPartialOrder SGe x =
  BinOp (BinOp (Lit $ Int 1) Equal x)
        COr
        (BinOp (Lit $ Int 0) Equal x)
mkPartialOrder SGt x = (BinOp (Lit $ Int 1) Equal x)

varPos :: LVar -> CodeGeneration Integer
varPos (Loc i) = return (toInteger i)
varPos (Glob name) = do
  positions <- globalVariablePositions <$> get
  case lookup name positions of
    (Just pos) -> return pos
    Nothing -> T.lift . Left $ "Invalid global variable id: " ++ show name

mkVarAccess :: Maybe ClassType -> LVar -> CodeGeneration Exp
mkVarAccess Nothing var = 
  (\ pos -> ArrayAccess $ ArrayIndex (contextArray var) (Lit $ Int pos)) 
  <$> varPos var
mkVarAccess (Just castTo) var = 
  Cast (RefType . ClassRefType $ castTo) <$> (mkVarAccess Nothing var)

mkPrimitiveCast :: ClassType -> ClassType -> LVar -> CodeGeneration Exp
mkPrimitiveCast fromType (ClassType [(toType, [])]) var =
  (\ var -> 
     MethodInv $ TypeMethodCall (J.Name [toType])
                                []
                                (Ident "valueOf")
                                [var]
  )
  <$> mkVarAccess (Just fromType) var

mkToString :: ClassType -> LVar -> CodeGeneration Exp
mkToString castTo var =
  (\ var -> MethodInv $ PrimaryMethodCall (var)
                                          []
                                          (Ident "toString")
                                          []
  )
  <$> mkVarAccess (Just castTo) var
data Std = In | Out | Err

instance Show Std where
  show In = "in"
  show Out = "out"
  show Err = "err"

mkSystemStd :: Std -> Exp
mkSystemStd std = FieldAccess $ PrimaryFieldAccess (ExpName $ J.Name [Ident "System"]) (Ident $ show std)

mkSystemOutPrint :: Exp -> Exp
mkSystemOutPrint value =
  MethodInv $ PrimaryMethodCall (mkSystemStd Out)
                                []
                                (Ident "print")
                                [value]

mkMathFun :: String -> LVar -> CodeGeneration Exp
mkMathFun funName var =
  (\ var -> MethodInv $ TypeMethodCall (J.Name [Ident "Double"])
                                       []
                                       (Ident "valueOf")
                                       [ MethodInv $ TypeMethodCall (J.Name [Ident "Math"])
                                                                    []
                                                                    (Ident funName)
                                                                    [var]
                                       ]
  )
  <$> mkVarAccess (Just doubleType) var

mkStringAtIndex :: LVar -> Exp -> CodeGeneration Exp
mkStringAtIndex var indexExp =
  (\ var -> MethodInv $ TypeMethodCall (J.Name [Ident "Integer"]) 
                                       []
                                       (Ident "valueOf")
                                       [ MethodInv $ PrimaryMethodCall (var)
                                                                       []
                                                                       (Ident "charAt")
                                                                       [indexExp]
                                       ]
  )
  <$> mkVarAccess (Just stringType) var

mkForeignType :: FType -> Maybe ClassType
mkForeignType (FArith (ATInt ity)) = return (intTyToClass ity)
mkForeignType (FArith ATFloat) = return doubleType
mkForeignType FChar = return integerType
mkForeignType FString = return stringType
mkForeignType FPtr = return objectType
mkForeignType FAny = return objectType
mkForeignType FUnit = Nothing

mkForeignVarAccess :: FType -> LVar -> CodeGeneration Exp
mkForeignVarAccess (FArith (ATInt ty)) var = 
  (\ var -> MethodInv $ PrimaryMethodCall var
                                          []
                                          (Ident (intTyToMethod ty))
                                          []
  )
  <$> mkVarAccess (Just $ intTyToClass ty) var
mkForeignVarAccess FChar var = Cast (PrimType CharT) <$> mkForeignVarAccess (FArith (ATInt (ITFixed IT32))) var
mkForeignVarAccess (FArith ATFloat) var = 
  (\ var -> MethodInv $ PrimaryMethodCall (var)
                                          []
                                          (Ident "doubleValue")
                                          []
  )
  <$> mkVarAccess (Just doubleType) var
mkForeignVarAccess otherType var = mkVarAccess (mkForeignType otherType) var 
 
mkFromForeignType :: FType -> Exp -> Exp
mkFromForeignType (FArith (ATInt ty)) from = 
  MethodInv $ TypeMethodCall (J.Name [intTyToIdent ty])
                             []
                             (Ident "valueOf")
                             [from]
mkFromForeignType FChar from = mkFromForeignType (FArith (ATInt (ITFixed IT32))) from
mkFromForeignType (FArith ATFloat) from =   
  MethodInv $ TypeMethodCall (J.Name [Ident "Double"])
                             []
                             (Ident "valueOf")
                             [from]
mkFromForeignType _ from = from

mkForeignInvoke :: FType -> String -> [(FType, LVar)] -> CodeGeneration Exp
mkForeignInvoke fType method args =
  (\ foreignInvokeMeth -> 
     MethodInv $ PrimaryMethodCall (InstanceCreation [] 
                                                     objectType 
                                                     [] 
                                                     (Just $ ClassBody [ MemberDecl $ foreignInvokeMeth ])
                                   )
                                   []
                                   (Ident "foreignInvoke")
                                   []
  )
  <$> mkForeignInvokeMethod fType method args


mkForeignInvokeMethod :: FType -> String -> [(FType, LVar)] -> CodeGeneration MemberDecl 
mkForeignInvokeMethod fType method args =
  (\ tryBlock -> 
    MethodDecl [Public, Final]
               []
               (Just . RefType $ ClassRefType objectType)
               (Ident "foreignInvoke")
               []
               []
               (MethodBody . Just $ Block 
                             [ BlockStmt 
                               $ Try tryBlock
                                   [ Catch (FormalParam [] 
                                                        (RefType $ ClassRefType exceptionType)
                                                        False
                                                        (VarId $ Ident "ex")
                                           )
                                           (Block [ BlockStmt 
                                                    . Throw
                                                    $ InstanceCreation []
                                                                       runtimeExceptionType
                                                                       [ExpName $ J.Name [Ident "ex"]]
                                                                       Nothing
                                                  ]
                                           )
                                   ]
                                   Nothing
                             ]
               )
  )
 <$> mkForeignInvokeTryBlock fType method args


mkForeignInvokeTryBlock :: FType -> String -> [(FType, LVar)] -> CodeGeneration Block
mkForeignInvokeTryBlock FUnit method args =
  (\ method args -> Block [ BlockStmt . ExpStmt . MethodInv $ MethodCall method args
                          , BlockStmt $ Return (Just $ Lit Null)
                          ]
  )
  <$> ( T.lift $ left (\ err -> "Error parsing name \"" ++ method ++ "\" :" ++ (show err))
                 (parser name method)
      )
  <*> mapM (uncurry mkForeignVarAccess) args
mkForeignInvokeTryBlock fType method args =
  (\ method args -> Block [ BlockStmt . Return 
                                 . Just 
                                 . mkFromForeignType fType
                                 . MethodInv 
                                 $ MethodCall method args
                          ]
  )
  <$> ( T.lift $ left (\ err -> "Error parsing name \"" ++ method ++ "\" :" ++ (show err))
                      (parser name method)
      )
  <*> mapM (uncurry mkForeignVarAccess) args

mkMethodClosure :: Name -> [LVar] -> CodeGeneration Exp
mkMethodClosure name args =
  (\ name args -> 
     InstanceCreation []
                      idrisClosureType
                      [ (ExpName $ J.Name [Ident "context"]) ]
                      ( Just 
                        $ ClassBody 
                            [ MemberDecl 
                              $ MethodDecl [Public, Final]
                                           []
                                           (Just . RefType $ ClassRefType objectType)
                                           (Ident "call")
                                           []
                                           []
                                           ( MethodBody 
                                             . Just 
                                             $ Block [ BlockStmt 
                                                       . Return 
                                                       . Just 
                                                       . MethodInv 
                                                       $ MethodCall (reverseNameSpace name) 
                                                                    args
                                                     ]
                                           )
                            ]
                      )
  )
  <$> mkName name
  <*> mapM (mkExp . SV) args

mkThread :: LVar -> CodeGeneration Exp
mkThread arg =
  (\ eval -> 
     MethodInv  
     $ PrimaryMethodCall (InstanceCreation [] 
                                           (ClassType [(Ident "Thread", [])]) 
                                           [ eval ] 
                                           ( Just 
                                             $ ClassBody [ MemberDecl 
                                                           $ MethodDecl [Public, Final]
                                                                        []
                                                                        (Just . RefType $ ClassRefType objectType)
                                                                        (Ident "_start")
                                                                        []
                                                                        []
                                                                        ( MethodBody 
                                                                          . Just 
                                                                          $ Block [ BlockStmt 
                                                                                    . ExpStmt 
                                                                                    . MethodInv 
                                                                                     $ MethodCall (J.Name [Ident "start"])
                                                                                                  []
                                                                                  , BlockStmt 
                                                                                    . Return 
                                                                                    . Just 
                                                                                    $ This
                                                                                  ]
                                                                        )
                                                         ]
                                           )
                         )
                         []
                         (Ident "_start")
                         []
  )
  <$> mkThreadBinding arg

mkThreadBinding :: LVar -> CodeGeneration Exp
mkThreadBinding var =
  (\ bindingMethod var ->
     MethodInv $ PrimaryMethodCall ( InstanceCreation []
                                                      objectType
                                                      []
                                                      (Just $ ClassBody [MemberDecl $ bindingMethod])
                                   )
                                   []
                                   (Ident "apply")
                                   [ var ]
  )
  <$> mkThreadBindingMethod
  <*> mkVarAccess Nothing var


mkThreadBindingMethod :: CodeGeneration MemberDecl
mkThreadBindingMethod = 
  (\ compute -> 
     MethodDecl [Final, Public]
                []
                (Just . RefType $ ClassRefType idrisClosureType)
                (Ident "apply")
                [ FormalParam [Final] (RefType . ClassRefType $ objectType) False (VarId $ Ident "param") ]
                []
                (MethodBody . Just $ Block
                            [ mkThreadBindingStack
                            , BlockStmt . Return $ Just compute
                            ]
                )
  )
  <$> mkBindingClosure (SUpdate (Loc 0) (SApp False (MN 0 "EVAL") [Loc 0]))


mkThreadBindingStack :: BlockStmt
mkThreadBindingStack =
  LocalVars [Final]
            objectArrayType
            [ VarDecl (VarDeclArray . VarId $ Ident "new_context")
                        (Just . InitArray $ ArrayInit [InitExp . ExpName $ J.Name [Ident "param"]])
            ]
 

mkExp :: SExp -> CodeGeneration Exp
mkExp (SV var) = mkVarAccess Nothing var
mkExp (SApp False name args) =
  (\ methClosure ->
     MethodInv $ PrimaryMethodCall ( InstanceCreation []
                                                      idrisTailCallClosureType
                                                      [ methClosure ]
                                                      Nothing
                                   )
                                   []
                                   (Ident "call")
                                   []
  )
  <$> mkMethodClosure name args
mkExp (SApp True name args) =
  (\ methClosure ->
     ( InstanceCreation []
                        idrisTailCallClosureType
                        [ methClosure ]
                        Nothing
     )
  )
  <$> mkMethodClosure name args
mkExp (SLet var new old) =
  mkLet var old new
mkExp (SUpdate var exp) =
  (\ rhs varPos -> Assign (ArrayLhs $ ArrayIndex (contextArray var) (Lit $ Int varPos))
                          EqualA
                          rhs
  )
  <$> mkExp exp
  <*> varPos var
mkExp (SCon conId name args) =
  (\ args -> InstanceCreation []
                              idrisObjectType
                              ((Lit $ Int (toInteger conId)):args)
                              Nothing)
  <$> mapM (mkExp .SV) args
mkExp (SCase var alts) = mkCase False var alts
mkExp (SChkCase var alts) = mkCase True var alts
mkExp (SProj var i) = mkProjection var i
mkExp (SConst (I x)) = 
  let x' :: Int32; x' = fromInteger (toInteger x) in
  return $ mkPrimitive "Integer" (Int (fromInteger (toInteger x')))
mkExp (SConst (BI x)) =
  return $ InstanceCreation [] 
                            (ClassType [(Ident "BigInteger", [])])
                            [Lit $ String (show x)]
                            Nothing
mkExp (SConst (Fl x)) = return $ mkPrimitive "Double" (Double x)
mkExp (SConst (Ch x)) = return $ mkPrimitive "Integer" (Char x)
mkExp (SConst (Str x)) = return $ Lit $ String x
mkExp (SConst (AType (ATInt ITNative))) = return $ mkClass integerType
mkExp (SConst (AType (ATInt ITBig))) = return $ mkClass bigIntegerType
mkExp (SConst (AType ATFloat)) = return $ mkClass doubleType
mkExp (SConst ChType) = return $ mkClass charType
mkExp (SConst StrType) = return $ mkClass stringType
mkExp (SConst (B8 x)) = return $ mkPrimitive "Byte" (String (show x))
mkExp (SConst (B16 x)) = return $ mkPrimitive "Short" (String (show x))
mkExp (SConst (B32 x)) = return $ mkPrimitive "Integer" (Int (toInteger x))
mkExp (SConst (B64 x)) = return $ mkPrimitive "Long" (String (show x))
mkExp (SConst (AType (ATInt (ITFixed IT8)))) = return $ mkClass byteType
mkExp (SConst (AType (ATInt (ITFixed IT16)))) = return $ mkClass shortType
mkExp (SConst (AType (ATInt (ITFixed IT32)))) = return $ mkClass integerType
mkExp (SConst (AType (ATInt (ITFixed IT64)))) = return $ mkClass longType
mkExp (SConst (PtrType)) = return $ mkClass objectType
mkExp (SConst (VoidType)) = return $ mkClass voidType
mkExp (SConst (Forgot)) = return $ mkClass objectType
mkExp (SForeign _ fType meth args) = mkForeignInvoke fType meth args
mkExp (SOp (LPlus (ATInt ITNative)) args) = mkExp (SOp (LPlus (ATInt (ITFixed IT32))) args)
mkExp (SOp (LMinus (ATInt ITNative)) args) = mkExp (SOp (LMinus (ATInt (ITFixed IT32))) args)
mkExp (SOp (LTimes (ATInt ITNative)) args) = mkExp (SOp (LTimes (ATInt (ITFixed IT32))) args)
mkExp (SOp (LSDiv (ATInt ITNative)) args) = mkExp (SOp (LSDiv (ATInt (ITFixed IT32))) args)
mkExp (SOp (LSRem (ATInt ITNative)) args) = mkExp (SOp (LSRem (ATInt (ITFixed IT32))) args)
mkExp (SOp (LAnd ITNative) args) = mkExp (SOp (LAnd (ITFixed IT32)) args)
mkExp (SOp (LOr ITNative) args) = mkExp (SOp (LOr (ITFixed IT32)) args)
mkExp (SOp (LXOr ITNative) args) = mkExp (SOp (LXOr (ITFixed IT32)) args)
mkExp (SOp (LCompl ITNative) args) = mkExp (SOp (LCompl (ITFixed IT32)) args)
mkExp (SOp (LSHL ITNative) args) = mkExp (SOp (LSHL (ITFixed IT32)) args)
mkExp (SOp (LASHR ITNative) args) = mkExp (SOp (LASHR (ITFixed IT32)) args)
mkExp (SOp (LEq (ATInt ITNative)) args) = mkExp (SOp (LEq (ATInt (ITFixed IT32))) args)
mkExp (SOp (LLt (ATInt ITNative)) args) = mkExp (SOp (LLt (ATInt (ITFixed IT32))) args)
mkExp (SOp (LLe (ATInt ITNative)) args) = mkExp (SOp (LLe (ATInt (ITFixed IT32))) args)
mkExp (SOp (LGt (ATInt ITNative)) args) = mkExp (SOp (LGt (ATInt (ITFixed IT32))) args)
mkExp (SOp (LGe (ATInt ITNative)) args) = mkExp (SOp (LGe (ATInt (ITFixed IT32))) args)
mkExp (SOp (LPlus ATFloat) args) = mkBinOpExp doubleType Add args
mkExp (SOp (LMinus ATFloat) args) = mkBinOpExp doubleType Sub args
mkExp (SOp (LTimes ATFloat) args) = mkBinOpExp doubleType Mult args
mkExp (SOp (LSDiv ATFloat) args) = mkBinOpExp doubleType Div args
mkExp (SOp (LEq ATFloat) args) = 
  mkMethodOpChain1 (mkBoolToNumber doubleType) doubleType "equals" args
mkExp (SOp (LLt ATFloat) args) = mkLogicalBinOpExp integerType LThan args
mkExp (SOp (LLe ATFloat) args) = mkLogicalBinOpExp integerType LThanE args
mkExp (SOp (LGt ATFloat) args) = mkLogicalBinOpExp integerType GThan args
mkExp (SOp (LGe ATFloat) args) = mkLogicalBinOpExp integerType GThanE args
mkExp (SOp (LPlus (ATInt ITBig)) args) = mkMethodOpChain1 id bigIntegerType "add" args
mkExp (SOp (LMinus (ATInt ITBig)) args) = mkMethodOpChain1 id bigIntegerType "subtract" args
mkExp (SOp (LTimes (ATInt ITBig)) args) = mkMethodOpChain1 id bigIntegerType "multiply" args
mkExp (SOp (LSDiv (ATInt ITBig)) args) = mkMethodOpChain1 id bigIntegerType "divide" args
mkExp (SOp (LSRem (ATInt ITBig)) args) = mkMethodOpChain1 id bigIntegerType "mod" args
mkExp (SOp (LEq (ATInt ITBig)) args) = 
  mkMethodOpChain1 (mkBoolToNumber bigIntegerType) bigIntegerType "equals" args
mkExp (SOp (LLt (ATInt ITBig)) args) =
  mkMethodOpChain1 ( mkBoolToNumber bigIntegerType 
                     . mkPartialOrder SLt
                   ) 
                   bigIntegerType 
                   "compareTo" 
                   args
mkExp (SOp (LLe (ATInt ITBig)) args) =
  mkMethodOpChain1 ( mkBoolToNumber bigIntegerType 
                   . mkPartialOrder SLe
                   ) 
                   bigIntegerType 
                   "compareTo" 
                   args
mkExp (SOp (LGt (ATInt ITBig)) args) =
  mkMethodOpChain1 ( mkBoolToNumber bigIntegerType 
                   . mkPartialOrder SGt
                   ) 
                   bigIntegerType 
                   "compareTo" 
                   args
mkExp (SOp (LGe (ATInt ITBig)) args) =
  mkMethodOpChain1 ( mkBoolToNumber bigIntegerType 
                   . mkPartialOrder SGe
                   ) 
                   bigIntegerType 
                   "compareTo" 
                   args
mkExp (SOp LStrConcat args) =
  mkMethodOpChain (\ exp -> InstanceCreation [] 
                                             (ClassType [(Ident "StringBuilder", [])])
                                             [exp]
                                             Nothing
                  )
                  (\ exp -> MethodInv $ PrimaryMethodCall exp [] (Ident "toString") [])
                  stringType 
                  "append"
                  args
mkExp (SOp LStrLt args@[_, _]) =
  mkMethodOpChain1 ( mkBoolToNumber integerType
                   . mkPartialOrder SLt
                   )
                   stringType
                   "compareTo"
                   args
mkExp (SOp LStrEq args@[_, _]) =
  mkMethodOpChain1 ( mkBoolToNumber integerType)
                   stringType
                   "equals"
                   args
mkExp (SOp LStrLen [arg]) =
  (\ var -> MethodInv $ PrimaryMethodCall var [] (Ident "length") [])
  <$> mkVarAccess (Just stringType) arg
mkExp (SOp (LIntFloat ity) [arg]) =
  mkPrimitiveCast (intTyToClass ity) doubleType arg
mkExp (SOp (LFloatInt ity) [arg]) =
  mkSignedExt (intTyToMethod ity) doubleType (intTyToClass ity) arg
mkExp (SOp (LIntStr ity) [arg]) =
  mkToString (intTyToClass ity) arg
mkExp (SOp (LStrInt ity) [arg]) =
  mkPrimitiveCast stringType (intTyToClass ity) arg
mkExp (SOp LFloatStr [arg]) =
  mkToString doubleType arg
mkExp (SOp LStrFloat [arg]) =
  mkPrimitiveCast doubleType stringType arg
mkExp (SOp (LSExt ITNative ITBig) [arg]) =
  mkPrimitiveCast integerType bigIntegerType arg
mkExp (SOp (LTrunc ITBig ITNative) [arg]) =
  mkPrimitiveCast bigIntegerType integerType arg
mkExp (SOp (LChInt ITNative) [arg]) =
  mkVarAccess (Just integerType) arg
mkExp (SOp (LIntCh ITNative) [arg]) =
  mkVarAccess (Just integerType) arg
mkExp (SOp LPrintNum [arg]) =
  mkSystemOutPrint <$> (mkVarAccess Nothing arg)
mkExp (SOp LPrintStr [arg]) =
  mkSystemOutPrint <$> (mkVarAccess (Just stringType) arg)
mkExp (SOp LReadStr [arg]) = mkExp (SForeign LANG_C FString "idris_readStr" [(FPtr, arg)])
mkExp (SOp (LLt (ATInt ty)) args) = mkLogicalBinOpExp (intTyToClass ty) LThan args
mkExp (SOp (LLe (ATInt ty)) args) = mkLogicalBinOpExp (intTyToClass ty) LThanE args
mkExp (SOp (LEq (ATInt ty)) args) = 
  mkMethodOpChain1 (mkBoolToNumber (intTyToClass ty)) (intTyToClass ty) "equals" args
mkExp (SOp (LGt (ATInt ty)) args) = mkLogicalBinOpExp (intTyToClass ty) GThan args
mkExp (SOp (LGe (ATInt ty)) args) = mkLogicalBinOpExp (intTyToClass ty) GThanE args
mkExp (SOp (LPlus (ATInt ty)) args) = mkBinOpExp (intTyToClass ty) Add args
mkExp (SOp (LMinus (ATInt ty)) args) = mkBinOpExp (intTyToClass ty) Sub args
mkExp (SOp (LTimes (ATInt ty)) args) = mkBinOpExp (intTyToClass ty) Mult args
mkExp (SOp (LUDiv (ITFixed IT64)) (arg:args)) = do
  (arg:args) <- mapM (mkVarAccess (Just longType)) (arg:args)
  return $ foldl (\ exp arg ->
                    MethodInv $ PrimaryMethodCall
                              ( MethodInv $ PrimaryMethodCall
                                            ( MethodInv $ TypeMethodCall (J.Name [Ident "BigInteger"])
                                                                         []
                                                                         (Ident "valueOf")
                                                                         [ exp ]
                                            )
                                            []
                                            (Ident "divide")
                                            [ MethodInv $ TypeMethodCall (J.Name [Ident "BigInteger"])
                                                                         []
                                                                         (Ident "valueOf")
                                                                         [ arg ]
                                            ]
                              )
                              []
                              (Ident "longValue")
                              []
                 )                                
           arg
           args
mkExp (SOp (LUDiv ty) args) = 
  mkBinOpExpConv (intTyToMethod $ nextIntTy ty) 
                 (intTyToPrimTy $ nextIntTy ty) 
                 (intTyToClass ty) 
                 Div 
                 args
mkExp (SOp (LSDiv (ATInt ty)) args) = mkBinOpExp (intTyToClass ty) Div args
mkExp (SOp (LURem (ITFixed IT64)) (arg:args)) = do
  (arg:args) <- mapM (mkVarAccess (Just longType)) (arg:args)
  return $ foldl (\ exp arg ->
                    MethodInv $ PrimaryMethodCall
                              ( MethodInv $ PrimaryMethodCall
                                            ( MethodInv $ TypeMethodCall (J.Name [Ident "BigInteger"])
                                                                         []
                                                                         (Ident "valueOf")
                                                                         [ exp ]
                                            )
                                            []
                                            (Ident "remainder")
                                            [ MethodInv $ TypeMethodCall (J.Name [Ident "BigInteger"])
                                                                         []
                                                                         (Ident "valueOf")
                                                                         [ arg ]
                                            ]
                              )
                              []
                              (Ident "longValue")
                              []
                 )                                
           arg
           args
mkExp (SOp (LURem ty) args) =
  mkBinOpExpConv (intTyToMethod $ nextIntTy ty) 
                 (intTyToPrimTy $ nextIntTy ty) 
                 (intTyToClass ty)
                 Rem
                 args
mkExp (SOp (LSRem (ATInt ty)) args) = mkBinOpExp (intTyToClass ty) Rem args
mkExp (SOp (LSHL ty) args) = mkBinOpExp (intTyToClass ty) LShift args
mkExp (SOp (LLSHR ty) args) = mkBinOpExp (intTyToClass ty) RRShift args
mkExp (SOp (LASHR ty) args) = mkBinOpExp (intTyToClass ty) RShift args
mkExp (SOp (LAnd ty) args) = mkBinOpExp (intTyToClass ty) And args
mkExp (SOp (LOr ty) args) = mkBinOpExp (intTyToClass ty) Or args
mkExp (SOp (LXOr ty) args) = mkBinOpExp (intTyToClass ty) Xor args
mkExp (SOp (LCompl ty) [var]) = PreBitCompl <$> mkVarAccess (Just $ intTyToClass ty) var
mkExp (SOp (LZExt from to) [var])
    | intTyWidth from < intTyWidth to
        = mkZeroExt (intTyToMethod to) (intTyWidth from) (intTyToClass from) (intTyToClass to) var
mkExp (SOp (LSExt from to) [var])
    | intTyWidth from < intTyWidth to
        = mkSignedExt (intTyToMethod to) (intTyToClass from) (intTyToClass to) var
mkExp (SOp (LTrunc from to) [var])
    | intTyWidth from > intTyWidth to
        = mkSignedExt (intTyToMethod to) (intTyToClass from) (intTyToClass to) var
mkExp (SOp LFExp [arg]) = mkMathFun "exp" arg
mkExp (SOp LFLog [arg]) = mkMathFun "log" arg
mkExp (SOp LFSin [arg]) = mkMathFun "sin" arg
mkExp (SOp LFCos [arg]) = mkMathFun "cos" arg
mkExp (SOp LFTan [arg]) = mkMathFun "tan" arg
mkExp (SOp LFASin [arg]) = mkMathFun "asin" arg
mkExp (SOp LFACos [arg]) = mkMathFun "acos" arg
mkExp (SOp LFATan [arg]) = mkMathFun "atan" arg
mkExp (SOp LFSqrt [arg]) = mkMathFun "sqrt" arg
mkExp (SOp LFFloor [arg]) = mkMathFun "floor" arg
mkExp (SOp LFCeil [arg]) = mkMathFun "ceil" arg
mkExp (SOp LStrHead [arg]) = mkStringAtIndex arg (Lit $ Int 0)
mkExp (SOp LStrTail [arg]) = 
  (\ var -> MethodInv $ PrimaryMethodCall (var)
                                         []
                                         (Ident "substring")
                                         [Lit $ Int 1]
  ) 
  <$> mkVarAccess (Just stringType) arg
mkExp (SOp LStrCons [c, cs]) =
  (\ cVar csVar -> MethodInv $ 
         PrimaryMethodCall ( MethodInv $ PrimaryMethodCall (InstanceCreation [] 
                                                                             (ClassType [(Ident "StringBuilder", [])])
                                                                             [csVar]
                                                                             Nothing
                                                           )
                                                           []
                                                           (Ident "insert")
                                                           [ Lit $ Int 0, 
                                                             Cast (PrimType CharT) 
                                                                  (MethodInv $ PrimaryMethodCall 
                                                                               (cVar)
                                                                               []
                                                                               (Ident "intValue")
                                                                               []
                                                                  )
                                                           ]
                           )
                           []
                           (Ident "toString")
                           []
 )
 <$> mkVarAccess (Just integerType) c
 <*> mkVarAccess (Just stringType) cs
mkExp (SOp LStrIndex [str, i]) = mkVarAccess (Just integerType) i >>= mkStringAtIndex str 
mkExp (SOp LStrRev [str]) = 
  (\ var -> MethodInv $ 
         PrimaryMethodCall ( MethodInv $ PrimaryMethodCall (InstanceCreation []
                                                                            (ClassType [(Ident "StringBuffer", [])])
                                                                            [var]
                                                                            Nothing
                                                           )
                                                           []
                                                           (Ident "reverse")
                                                           []
                           )
                           []
                           (Ident "toString")
                           []
  )
  <$> mkVarAccess (Just stringType) str
mkExp (SOp LStdIn []) = return $ mkSystemStd In
mkExp (SOp LStdOut []) = return $ mkSystemStd Out
mkExp (SOp LStdErr []) = return $ mkSystemStd Err
mkExp (SOp LFork [arg]) = mkThread arg
mkExp (SOp LPar [arg]) = mkExp (SV arg)
mkExp (SOp LVMPtr []) = 
  return $ MethodInv $ TypeMethodCall (J.Name [Ident "Thread"]) [] (Ident "currentThread") []
mkExp (SOp LNoOp args) = mkExp . SV $ last args
mkExp (SNothing) = return $ Lit Null
mkExp (SError err) =
  return . MethodInv $ 
         PrimaryMethodCall (InstanceCreation [] 
                                             runtimeExceptionType 
                                             [Lit $ String err]
                                             ( Just $ ClassBody
                                                    [ MemberDecl $ MethodDecl [Public, Final]
                                                                              []
                                                                              (Just . RefType $ ClassRefType objectType)
                                                                              (Ident "throwSelf")
                                                                              []
                                                                              []
                                                                              ( MethodBody . Just $
                                                                                          Block [ BlockStmt (Throw This) ]
                                                                              )
                                                     ]
                                             )
                           )
                           []
                           (Ident "throwSelf")
                           []
mkExp other = error (show other)
