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
import           Data.Char
import           Data.Maybe (fromJust)
import           Language.Java.Parser
import           Language.Java.Pretty
import           Language.Java.Syntax hiding (Name)
import qualified Language.Java.Syntax as J
import           System.Directory
import           System.Exit
import           System.FilePath
import           System.IO
import           System.Process

codegenJava :: [(Name, SDecl)] ->
               FilePath -> -- output file name
               OutputType ->
               IO ()
codegenJava defs out exec =
  either (error)
         (writeFile out . flatIndent . prettyPrint)
         (mkCompilationUnit defs out)

mkCompilationUnit :: [(Name, SDecl)] ->
                     FilePath ->
                     Either String CompilationUnit
mkCompilationUnit defs out =
  CompilationUnit Nothing [ ImportDecl False idrisRts True
                          , ImportDecl True idrisForeign True
                          , ImportDecl False bigInteger False
                          , ImportDecl False stringBuffer False
                          , ImportDecl False runtimeException False
                          , ImportDecl False scanner False
                          , ImportDecl False arrays False
                          ] <$>
                  mkTypeDecl defs out
  where
    idrisRts = J.Name $ map Ident ["org", "idris", "rts"]
    idrisForeign = J.Name $ map Ident ["org", "idris", "rts", "ForeignPrimitives"]
    bigInteger = J.Name $ map Ident ["java", "math", "BigInteger"]
    stringBuffer = J.Name $ map Ident ["java", "lang", "StringBuffer"]
    runtimeException = J.Name $ map Ident ["java", "lang", "RuntimeException"]
    scanner = J.Name $ map Ident ["java", "util", "Scanner"]
    arrays = J.Name $ map Ident ["java", "util", "Arrays"]

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

mkTypeDecl :: [(Name, SDecl)] ->
              FilePath ->
              Either String [TypeDecl]
mkTypeDecl defs out =
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
        >>= (\ ident -> mkClassBody (map (second (prefixCallNamespacesDecl ident)) defs))
      )

mkClassName :: FilePath -> Either String Ident
mkClassName path =
  left (\ err -> "Parser error in \"" ++ path ++ "\": " ++ (show err))
       (parser ident . takeBaseName $ takeFileName path)

mkClassBody :: [(Name, SDecl)] ->
               Either String ClassBody
mkClassBody defs = (ClassBody . addMainMethod . mergeInnerClasses)
                   <$> mapM mkDecl defs

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
mergeInnerClasses = foldl mergeInner []
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


mkIdentifier :: Name -> Either String Ident
mkIdentifier (NS name _) = mkIdentifier name
mkIdentifier (MN i name) = (\ (Ident x) -> Ident $ x ++ ('_' : show i))
                           <$> mkIdentifier (UN name)
mkIdentifier (UN name) =
  left (\ err -> "Parser error in \"" ++ name ++ "\": " ++ (show err))
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

    cleanReserved x = x

mkName :: Name -> Either String J.Name
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

--idrisFunctionType :: ClassType
--idrisFunctionType = ClassType [(Ident "IdrisFunction", [])]

idrisObjectType :: ClassType
idrisObjectType = ClassType [(Ident "IdrisObject", [])]

contextArray :: Exp
contextArray = ExpName $ J.Name [Ident "context"]

charType :: ClassType
charType = ClassType [(Ident "Character", [])]

byteType :: ClassType
byteType = ClassType [(Ident "Byte", [])]

shortType :: ClassType
shortType = ClassType [(Ident "Short", [])]

integerType :: ClassType
integerType = ClassType [(Ident "Integer", [])]

longType :: ClassType
longType = ClassType [(Ident "Integer", [])]

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

mkDecl :: (Name, SDecl) ->
          Either String Decl
mkDecl ((NS n (ns:nss)), decl) =
  (\ name body -> MemberDecl $ MemberClassDecl $ ClassDecl [Public, Static] name [] Nothing [] body)
  <$> mkIdentifier (UN ns)
  <*> mkClassBody [(NS n nss, decl)]
mkDecl (_, SFun name params stackSize body) =
  (\ name params cont ->
     MemberDecl $ MethodDecl [Public, Static]
                             []
                             (Just . RefType $ ClassRefType objectType)
                             name
                             params
                             []
                             (MethodBody . Just $ Block [ BlockStmt . Return . Just . MethodInv $
                                                                    PrimaryMethodCall cont [] (Ident "call") []])
  )
  <$> mkIdentifier name
  <*> mapM mkFormalParam params
  <*> mkClosure params stackSize body


mkClosure :: [Name] -> Int -> SExp -> Either String Exp
mkClosure params stackSize body =
  (\ paramArray body -> 
     InstanceCreation [] 
                      idrisClosureType 
                      [paramArray]
                      (Just $ ClassBody [body])
  )
  <$> mkStackInit params stackSize
  <*> mkClosureCall body

mkFormalParam :: Name -> Either String FormalParam
mkFormalParam name =
  (\ name -> FormalParam [Final] (RefType . ClassRefType $ objectType) False (VarId name))
  <$> mkIdentifier name

mkClosureCall :: SExp -> Either String Decl
mkClosureCall body =
  (\ body -> MemberDecl $ MethodDecl [Public] [] (Just . RefType $ ClassRefType objectType) (Ident "call") [] [] body)
  <$> mkMethodBody body

mkMethodBody :: SExp -> Either String MethodBody
mkMethodBody exp =
  (\ exp -> MethodBody . Just . Block $ [BlockStmt . Return . Just $ exp])
  <$> mkExp exp

mkStackInit :: [Name] -> Int -> Either String Exp
mkStackInit params stackSize =
  (\ localVars -> ArrayCreateInit objectArrayType 0 . ArrayInit $
                  (map (InitExp . ExpName) localVars)
                  ++ (replicate (stackSize) (InitExp $ Lit Null)))
  <$> mapM mkName params

mkAnonymousLetBinding :: LVar -> SExp -> SExp -> Either String Exp
mkAnonymousLetBinding var oldExp newExp =
  (\ bindingMethod newExp ->
     MethodInv $ PrimaryMethodCall 
                 ( MethodInv $ PrimaryMethodCall ( InstanceCreation []
                                                                    objectType
                                                                    []
                                                                    (Just $ ClassBody [MemberDecl $ bindingMethod])
                                                 )
                                                 []
                                                 (Ident "apply")
                                                 [ contextArray
                                                 , newExp]
                 )
                 []
                 (Ident "call")
                 []
  )                                 
  <$> mkLetBindingMethod var oldExp
  <*> mkExp newExp


mkContextParam :: FormalParam
mkContextParam = 
  FormalParam [Final] (objectArrayType) False (VarId (Ident "context"))

mkLetBindingMethod :: LVar -> SExp -> Either String MemberDecl
mkLetBindingMethod  (Loc i) oldExp = 
  (\ param bindingStack oldCont -> 
     MethodDecl [Final, Public]
                []
                (Just . RefType $ ClassRefType idrisClosureType)
                (Ident "apply")
                [mkContextParam, param]
                []
                (MethodBody . Just . Block $
                            bindingStack ++ [BlockStmt . Return $ Just oldCont]
                )
  )
  <$> mkFormalParam (UN "param")
  <*> mkBindingStack True i [UN "param"]
  <*> mkBindingClosure oldExp

mkBindingClosure :: SExp -> Either String Exp
mkBindingClosure oldExp =
  (\ oldCall -> 
     InstanceCreation [] 
                      idrisClosureType
                      [ ExpName $ J.Name [Ident "new_context"] ]
                      (Just $ ClassBody [oldCall])
  )
  <$> mkClosureCall oldExp


mkBindingStack :: Bool -> Int -> [Name] -> Either String [BlockStmt]
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
                         
reverseNameSpace :: J.Name -> J.Name
reverseNameSpace (J.Name ids) =
  J.Name ((tail ids) ++ [head ids])

mkCase :: Bool -> LVar -> [SAlt] -> Either String Exp
mkCase checked var ((SConCase parentStackPos consIndex _ params branchExpression):cases) =
  mkConsCase checked
             var
             parentStackPos 
             consIndex 
             params 
             branchExpression
             (SCase var cases)
mkCase checked var (c@(SConstCase constant branchExpression):cases) =
  (\ constant branchExpression alternative -> 
     Cond ( MethodInv $ PrimaryMethodCall (constant)
                                          []
                                          (Ident "equals")
                                          [mkVarAccess Nothing var]
          )
          branchExpression
          alternative
  )
  <$> mkExp (SConst constant)
  <*> mkExp branchExpression
  <*> mkCase checked var cases
mkCase checked var (SDefaultCase exp:cases) = mkExp exp
mkCase checked  _ [] = mkExp (SError "Non-exhaustive pattern")

mkConsCase :: Bool -> LVar -> Int -> Int -> [Name] -> SExp -> SExp -> Either String Exp
mkConsCase checked
           toDeconstruct
           parentStackStart 
           consIndex 
           params 
           branchExpression 
           alternative =
  (\ caseBinding alternative-> 
     Cond (BinOp (InstanceOf (mkVarAccess Nothing toDeconstruct) 
                             (ClassRefType idrisObjectType)
                 )
                 CAnd
                 ( BinOp
                   ( MethodInv $ PrimaryMethodCall (mkVarAccess (Just idrisObjectType) toDeconstruct)
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


mkCaseBinding :: Bool -> LVar -> Int -> [Name] -> SExp -> Either String Exp
mkCaseBinding checked var parentStackStart params branchExpression =
  (\ bindingMethod ->
     MethodInv $ PrimaryMethodCall 
               ( MethodInv $ PrimaryMethodCall (InstanceCreation []
                                                                 (ClassType [(Ident "Object", [])])
                                                                 []
                                                                 (Just $ ClassBody [MemberDecl $ bindingMethod])
                                               )
                                               []
                                               (Ident "apply")
                                               ( contextArray
                                                 : (mkCaseBindingDeconstruction var params) 
                                               )
               )
               []
               (Ident "call")
               []
  )
  <$> mkCaseBindingMethod checked parentStackStart params branchExpression



mkCaseBindingMethod :: Bool -> Int -> [Name] -> SExp -> Either String MemberDecl
mkCaseBindingMethod checked parentStackStart params branchExpression =
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
  <*> mkBindingStack checked parentStackStart params
  <*> mkBindingClosure branchExpression

mkCaseBindingDeconstruction :: LVar -> [Name] -> [Exp]
mkCaseBindingDeconstruction var members =
  map (mkProjection var) ([0..(length members - 1)])

mkProjection :: LVar -> Int -> Exp
mkProjection var memberNr =
  ArrayAccess $ ArrayIndex ( MethodInv $ PrimaryMethodCall
                                           (mkVarAccess (Just idrisObjectType) var)
                                           []
                                           (Ident "getData")
                                           []
                           )
                           (Lit $ Int (toInteger memberNr))

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

mkBinOpExp :: ClassType -> Op -> [LVar] -> Exp
mkBinOpExp castTo op (var:vars) = 
  foldl (\ exp -> BinOp exp op . mkVarAccess (Just castTo)) 
        (mkVarAccess (Just castTo) var) 
        vars

mkBinOpExpTrans :: (Exp -> Exp) -> (Exp -> Exp) -> ClassType -> Op -> [LVar] -> Exp
mkBinOpExpTrans opTransformation resultTransformation castTo op (var:vars) =
    foldl (\ exp -> resultTransformation 
                    . BinOp (opTransformation exp) op 
                    . opTransformation 
                    . mkVarAccess (Just castTo)) 
        (mkVarAccess (Just castTo) var)
        vars

mkBinOpExpConv :: String -> PrimType -> ClassType -> Op -> [LVar] -> Exp
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

mkLogicalBinOpExp :: ClassType -> Op -> [LVar] -> Exp
mkLogicalBinOpExp castTo op (var:vars) =
  foldl (\ exp -> mkBoolToNumber castTo . BinOp exp op . mkVarAccess (Just castTo)) 
        (mkVarAccess (Just castTo) var) 
        vars

mkMethodOpChain1 :: (Exp -> Exp) -> ClassType -> String -> [LVar] -> Exp
mkMethodOpChain1 = mkMethodOpChain id

mkMethodOpChain :: (Exp -> Exp) -> (Exp -> Exp) -> ClassType -> String -> [LVar] -> Exp
mkMethodOpChain initialTransformation resultTransformation castTo method (arg:args) =
  foldl (\ exp arg' -> 
           resultTransformation . MethodInv $ PrimaryMethodCall exp
                                                                []
                                                                (Ident method)
                                                                [mkVarAccess (Just $ castTo) arg']
        )
        (initialTransformation (mkVarAccess (Just $ castTo) arg))
        args

mkBoolToNumber :: ClassType -> Exp -> Exp
mkBoolToNumber (ClassType [(Ident name, [])]) boolExp =
  Cond boolExp (mkPrimitive name (Int 1)) (mkPrimitive name (Int 0))

mkZeroExt :: String -> Int -> ClassType -> ClassType -> LVar -> Exp
mkZeroExt toMethod bits fromType toType@(ClassType [(toTypeName, [])]) var = 
  MethodInv $ TypeMethodCall (J.Name [toTypeName])
                             []
                             (Ident "valueOf")
                             [ Cond ( BinOp (mkVarAccess (Just $ fromType) var)
                                            LThan
                                            (Lit $ Int 0)
                                    )
                                    ( BinOp (Lit $ Int (2^bits))
                                            Add
                                            (mkSignedExt' toMethod fromType var)
                                    )
                               (mkSignedExt' toMethod fromType var)
                             ]
  
mkSignedExt :: String -> ClassType -> ClassType -> LVar -> Exp
mkSignedExt toMethod fromType (ClassType [(toTypeName, [])]) var =
  MethodInv $ TypeMethodCall (J.Name [toTypeName])
                             []
                             (Ident "valueOf")
                             [ mkSignedExt' toMethod fromType var ]

mkSignedExt' :: String -> ClassType -> LVar -> Exp
mkSignedExt' toMethod fromType var =
  MethodInv $ PrimaryMethodCall (mkVarAccess (Just $ fromType) var)
                                [] 
                                (Ident toMethod)
                                []

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

mkVarAccess :: Maybe ClassType -> LVar -> Exp
mkVarAccess Nothing (Loc i) = 
  ArrayAccess $ ArrayIndex contextArray (Lit $ Int (toInteger i))
mkVarAccess (Just castTo) var = 
  Cast (RefType . ClassRefType $ castTo) (mkVarAccess Nothing var)

mkPrimitiveCast :: ClassType -> ClassType -> LVar -> Exp
mkPrimitiveCast fromType (ClassType [(toType, [])]) var =
  MethodInv $ TypeMethodCall (J.Name [toType])
                             []
                             (Ident "valueOf")
                             [mkVarAccess (Just fromType) var]

mkToString :: ClassType -> LVar -> Exp
mkToString castTo var =
  MethodInv $ PrimaryMethodCall (mkVarAccess (Just castTo) var)
                                []
                                (Ident "toString")
                                []

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

mkMathFun :: String -> LVar -> Exp
mkMathFun funName var =
  MethodInv $ TypeMethodCall (J.Name [Ident "Double"])
                             []
                             (Ident "valueOf")
                             [ MethodInv $ TypeMethodCall (J.Name [Ident "Math"])
                                                          []
                                                          (Ident funName)
                                                          [mkVarAccess (Just doubleType) var]
                             ]

mkStringAtIndex :: LVar -> Exp -> Exp
mkStringAtIndex var indexExp =
  MethodInv $ TypeMethodCall (J.Name [Ident "Integer"]) 
                                     []
                                     (Ident "valueOf")
                                     [ MethodInv $ PrimaryMethodCall (mkVarAccess (Just stringType) var)
                                                                     []
                                                                     (Ident "charAt")
                                                                     [indexExp]
                                     ]

mkForeignType :: FType -> Maybe ClassType
mkForeignType FInt = return $ integerType
mkForeignType FChar = return $ integerType
mkForeignType FString = return $ stringType
mkForeignType FPtr = return $ objectType
mkForeignType FDouble = return $ doubleType
mkForeignType FAny = return $ objectType
mkForeignType FUnit = Nothing

mkForeignVarAccess :: FType -> LVar -> Exp
mkForeignVarAccess FInt var = 
  MethodInv $ PrimaryMethodCall (mkVarAccess (Just integerType) var)
                                []
                                (Ident "intValue")
                                []
mkForeignVarAccess FChar var = Cast (PrimType CharT) (mkForeignVarAccess FInt var)
mkForeignVarAccess FDouble var = 
  MethodInv $ PrimaryMethodCall (mkVarAccess (Just doubleType) var)
                                []
                                (Ident "doubleValue")
                                []
mkForeignVarAccess otherType var = mkVarAccess (mkForeignType otherType) var 
 
mkFromForeignType :: FType -> Exp -> Exp
mkFromForeignType FInt from = 
  MethodInv $ TypeMethodCall (J.Name [Ident "Integer"])
                             []
                             (Ident "valueOf")
                             [from]
mkFromForeignType FChar from = mkFromForeignType FInt from
mkFromForeignType FDouble from =   
  MethodInv $ TypeMethodCall (J.Name [Ident "Double"])
                             []
                             (Ident "valueOf")
                             [from]
mkFromForeignType _ from = from

mkForeignInvoke :: FType -> String -> [(FType, LVar)] -> Either String Exp
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


mkForeignInvokeMethod :: FType -> String -> [(FType, LVar)] -> Either String MemberDecl 
mkForeignInvokeMethod fType method args =
  (\ tryBlock -> 
    MethodDecl [Public, Final]
               []
               (Just . RefType $ ClassRefType objectType)
               (Ident "foreignInvoke")
               []
               []
               (MethodBody . Just $ Block [ BlockStmt $ 
                                                      Try tryBlock
                                                          [ Catch (FormalParam [] 
                                                                               (RefType $ ClassRefType exceptionType)
                                                                               False
                                                                               (VarId $ Ident "ex")
                                                                  )
                                                                  (Block [ BlockStmt . Throw $
                                                                                     InstanceCreation []
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


mkForeignInvokeTryBlock :: FType -> String -> [(FType, LVar)] -> Either String Block
mkForeignInvokeTryBlock FUnit method args =
  (\ method -> Block [ BlockStmt . ExpStmt . MethodInv $ 
                                 MethodCall method
                                            (map (uncurry mkForeignVarAccess) args)
                     , BlockStmt $ Return (Just $ Lit Null)
                     ]
  )
  <$> ( left (\ err -> "Error parsing name \"" ++ method ++ "\" :" ++ (show err))
             (parser name method)
      )
mkForeignInvokeTryBlock fType method args =
  (\ method -> Block [ BlockStmt . Return 
                                 . Just 
                                 . mkFromForeignType fType
                                 . MethodInv $ 
                                   MethodCall method
                                                (map (uncurry mkForeignVarAccess) args)
                     ]
  )
  <$> ( left (\ err -> "Error parsing name \"" ++ method ++ "\" :" ++ (show err))
             (parser name method)
      )

mkMethodClosure :: Name -> [LVar] -> Either String Exp
mkMethodClosure name args =
  (\ name args -> 
     InstanceCreation []
                      idrisClosureType
                      [ (ExpName $ J.Name [Ident "context"]) ]
                      ( Just $ ClassBody 
                               [ MemberDecl $ 
                                            MethodDecl [Public, Final]
                                                       []
                                                       (Just . RefType $ ClassRefType objectType)
                                                       (Ident "call")
                                                       []
                                                       []
                                                       ( MethodBody . Just $ 
                                                                    Block [ BlockStmt . Return . Just . MethodInv $ 
                                                                                      MethodCall (reverseNameSpace name) 
                                                                                                 args
                                                                          ]
                                                       )
                               ]
                        )
  )
  <$> mkName name
  <*> mapM (mkExp . SV) args

mkThread :: LVar -> Either String Exp
mkThread arg =
  (\ eval -> MethodInv $ 
         PrimaryMethodCall (InstanceCreation [] 
                                             (ClassType [(Ident "Thread", [])]) 
                                             [ eval  ] 
                                             ( Just $ ClassBody
                                                      [ MemberDecl $ MethodDecl 
                                                                     [Public, Final]
                                                                     []
                                                                     (Just . RefType $ ClassRefType objectType)
                                                                     (Ident "_start")
                                                                     []
                                                                     []
                                                                     ( MethodBody . Just $ Block
                                                                                  [ BlockStmt . ExpStmt . MethodInv $ MethodCall
                                                                                              (J.Name [Ident "start"])
                                                                                              []
                                                                                  , BlockStmt . Return . Just $ This
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

mkThreadBinding :: LVar -> Either String Exp
mkThreadBinding var =
  (\ bindingMethod ->
     MethodInv $ PrimaryMethodCall ( InstanceCreation []
                                                      objectType
                                                      []
                                                      (Just $ ClassBody [MemberDecl $ bindingMethod])
                                   )
                                   []
                                   (Ident "apply")
                                   [ mkVarAccess Nothing var  ]
  )                                 
  <$> mkThreadBindingMethod


mkThreadBindingMethod :: Either String MemberDecl
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
 

mkExp :: SExp -> Either String Exp
mkExp (SV var) =
  return $ mkVarAccess Nothing var
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
  mkAnonymousLetBinding var old new
mkExp (SUpdate (Loc i) exp) =
  (\ rhs -> Assign (ArrayLhs $ ArrayIndex (contextArray) (Lit $ Int (toInteger i)))
                   EqualA
                   rhs)
  <$> mkExp exp
mkExp (SCon conId name args) =
  (\ args -> InstanceCreation []
                              idrisObjectType
                              ((Lit $ Int (toInteger conId)):args)
                              Nothing)
  <$> mapM (mkExp .SV) args
mkExp (SCase var alts) = mkCase False var alts
mkExp (SChkCase var alts) = mkCase True var alts
mkExp (SProj var i) = return $ mkProjection var i
mkExp (SConst (I x)) = return $ mkPrimitive "Integer" (Int (toInteger x))
mkExp (SConst (BI x)) =
  return $ InstanceCreation [] 
                            (ClassType [(Ident "BigInteger", [])])
                            [Lit $ String (show x)]
                            Nothing
mkExp (SConst (Fl x)) = return $ mkPrimitive "Double" (Double x)
mkExp (SConst (Ch x)) = return $ mkPrimitive "Integer" (Char x)
mkExp (SConst (Str x)) = return $ Lit $ String x
mkExp (SConst IType) = return $ mkClass integerType
mkExp (SConst BIType) = return $ mkClass bigIntegerType
mkExp (SConst FlType) = return $ mkClass doubleType
mkExp (SConst ChType) = return $ mkClass charType
mkExp (SConst StrType) = return $ mkClass stringType
mkExp (SConst (B8 x)) = return $ mkPrimitive "Byte" (Int (toInteger x))
mkExp (SConst (B16 x)) = return $ mkPrimitive "Short" (Int (toInteger x))
mkExp (SConst (B32 x)) = return $ mkPrimitive "Integer" (Int (toInteger x))
mkExp (SConst (B64 x)) = return $ mkPrimitive "Long" (Int (toInteger x))
mkExp (SConst (B8Type))= return $ mkClass byteType
mkExp (SConst (B16Type)) = return $ mkClass shortType
mkExp (SConst (B32Type)) = return $ mkClass integerType
mkExp (SConst (B64Type)) = return $ mkClass longType
mkExp (SConst (PtrType)) = return $ mkClass objectType
mkExp (SConst (VoidType)) = return $ mkClass voidType
mkExp (SConst (Forgot)) = return $ mkClass objectType
mkExp (SForeign _ fType meth args) = mkForeignInvoke fType meth args
mkExp (SOp LPlus args) = return $ mkBinOpExp integerType Add args
mkExp (SOp LMinus args) = return $ mkBinOpExp integerType Sub args
mkExp (SOp LTimes args) = return $ mkBinOpExp integerType Mult args
mkExp (SOp LDiv args) = return $ mkBinOpExp integerType Div args
mkExp (SOp LMod args) = return $ mkBinOpExp integerType Rem args
mkExp (SOp LAnd args) = return $ mkBinOpExp integerType And args
mkExp (SOp LOr args) = return $ mkBinOpExp integerType Or args
mkExp (SOp LXOr args) = return $ mkBinOpExp integerType Xor args
mkExp (SOp LCompl [var]) = 
  return $ PreBitCompl (mkVarAccess (Just $ integerType) var)
mkExp (SOp LSHL args) = return $ mkBinOpExp integerType LShift args
mkExp (SOp LSHR args) = return $ mkBinOpExp integerType RShift args
mkExp (SOp LEq args) = 
  return $ mkMethodOpChain1 (mkBoolToNumber integerType) objectType "equals" args
mkExp (SOp LLt args) = return $ mkLogicalBinOpExp integerType LThan args
mkExp (SOp LLe args) = return $ mkLogicalBinOpExp integerType LThanE args
mkExp (SOp LGt args) = return $ mkLogicalBinOpExp integerType GThan args
mkExp (SOp LGe args) = return $ mkLogicalBinOpExp integerType GThanE args
mkExp (SOp LFPlus args) = return $ mkBinOpExp doubleType Add args
mkExp (SOp LFMinus args) = return $ mkBinOpExp doubleType Sub args
mkExp (SOp LFTimes args) = return $ mkBinOpExp doubleType Mult args
mkExp (SOp LFDiv args) = return $ mkBinOpExp doubleType Div args
mkExp (SOp LFEq args) = 
  return $ mkMethodOpChain1 (mkBoolToNumber doubleType) doubleType "equals" args
mkExp (SOp LFLt args) = return $ mkLogicalBinOpExp integerType LThan args
mkExp (SOp LFLe args) = return $ mkLogicalBinOpExp integerType LThanE args
mkExp (SOp LFGt args) = return $ mkLogicalBinOpExp integerType GThan args
mkExp (SOp LFGe args) = return $ mkLogicalBinOpExp integerType GThanE args
mkExp (SOp LBPlus args) = return $ mkMethodOpChain1 id bigIntegerType "add" args
mkExp (SOp LBMinus args) = return $ mkMethodOpChain1 id bigIntegerType "subtract" args
mkExp (SOp LBTimes args) = return $ mkMethodOpChain1 id bigIntegerType "multiply" args
mkExp (SOp LBDiv args) = return $ mkMethodOpChain1 id bigIntegerType "divide" args
mkExp (SOp LBMod args) = return $ mkMethodOpChain1 id bigIntegerType "mod" args
mkExp (SOp LBEq args) = 
  return $ mkMethodOpChain1 (mkBoolToNumber bigIntegerType) bigIntegerType "equals" args
mkExp (SOp LBLt args) = 
  return $ mkMethodOpChain1 ( mkBoolToNumber bigIntegerType 
                            . mkPartialOrder SLt
                            ) 
                            bigIntegerType 
                            "compare" 
                            args
mkExp (SOp LBLe args) = 
  return $ mkMethodOpChain1 ( mkBoolToNumber bigIntegerType 
                            . mkPartialOrder SLe
                            ) 
                            bigIntegerType 
                            "compare" 
                            args
mkExp (SOp LBGt args) = 
  return $ mkMethodOpChain1 ( mkBoolToNumber bigIntegerType 
                            . mkPartialOrder SGt
                            ) 
                            bigIntegerType 
                            "compare" 
                            args
mkExp (SOp LBGe args) = 
  return $ mkMethodOpChain1 ( mkBoolToNumber bigIntegerType 
                            . mkPartialOrder SGe
                            ) 
                            bigIntegerType 
                            "compare" 
                            args
mkExp (SOp LStrConcat args) =
  return $ mkMethodOpChain (\ exp -> 
                              InstanceCreation [] 
                                               (ClassType [(Ident "StringBuilder", [])])
                                               [exp]
                                               Nothing
                           )
                           (\ exp -> MethodInv $ PrimaryMethodCall exp [] (Ident "toString") [])
                           stringType 
                           "append"
                           args
mkExp (SOp LStrLt args@[_, _]) =
  return $ mkMethodOpChain1 ( mkBoolToNumber integerType
                            . mkPartialOrder SLt
                            )
                            stringType
                            "compare"
                            args
mkExp (SOp LStrEq args@[_, _]) =
  return $ mkMethodOpChain1 ( mkBoolToNumber integerType)
                            stringType
                            "equals"
                            args
mkExp (SOp LStrLen [arg]) = 
  return . MethodInv $ PrimaryMethodCall (mkVarAccess (Just stringType) arg) [] (Ident "length") []
mkExp (SOp LIntFloat [arg]) =
  return $ mkPrimitiveCast integerType doubleType arg
mkExp (SOp LFloatInt [arg]) =
  return $ mkPrimitiveCast doubleType integerType arg
mkExp (SOp LIntStr [arg]) =
  return $ mkToString integerType arg
mkExp (SOp LStrInt [arg]) =
  return $ mkPrimitiveCast stringType integerType arg
mkExp (SOp LFloatStr [arg]) =
  return $ mkToString doubleType arg
mkExp (SOp LStrFloat [arg]) =
  return $ mkPrimitiveCast doubleType stringType arg
mkExp (SOp LIntBig [arg]) =
  return $ mkPrimitiveCast integerType bigIntegerType arg
mkExp (SOp LBigInt [arg]) =
  return $ mkPrimitiveCast bigIntegerType integerType arg
mkExp (SOp LStrBig [arg]) =
  return $ InstanceCreation [] bigIntegerType [mkVarAccess (Just stringType) arg] Nothing
mkExp (SOp LBigStr [arg]) =
  return $ mkToString bigIntegerType arg
mkExp (SOp LChInt [arg]) =
  return $ mkVarAccess (Just integerType) arg
mkExp (SOp LIntCh [arg]) =
  return $ mkVarAccess (Just integerType) arg
mkExp (SOp LPrintNum [arg]) =
  return $ mkSystemOutPrint (mkVarAccess Nothing arg)
mkExp (SOp LPrintStr [arg]) =
  return $ mkSystemOutPrint (mkVarAccess (Just stringType) arg)
mkExp (SOp LReadStr [arg]) = mkExp (SForeign LANG_C FString "idris_readStr" [(FPtr, arg)])
mkExp (SOp LB8Lt args) = return $ mkLogicalBinOpExp byteType LThan args
mkExp (SOp LB8Lte args) = return $ mkLogicalBinOpExp byteType LThanE args
mkExp (SOp LB8Eq args) = 
  return $ mkMethodOpChain1 (mkBoolToNumber byteType) byteType "equals" args
mkExp (SOp LB8Gt args) = return $ mkLogicalBinOpExp byteType GThan args
mkExp (SOp LB8Gte args) = return $ mkLogicalBinOpExp byteType GThanE args
mkExp (SOp LB8Plus args) = return $ mkBinOpExp byteType Add args
mkExp (SOp LB8Minus args) = return $ mkBinOpExp byteType Sub args
mkExp (SOp LB8Times args) = return $ mkBinOpExp byteType Mult args
mkExp (SOp LB8UDiv args) = return $ mkBinOpExpConv "shortValue" ShortT byteType Div args
mkExp (SOp LB8SDiv args) = return $ mkBinOpExp byteType Div args
mkExp (SOp LB8URem args) = return $ mkBinOpExpConv "shortValue" ShortT byteType Rem args
mkExp (SOp LB8SRem args) = return $ mkBinOpExp byteType Rem args
mkExp (SOp LB8Shl args) = return $ mkBinOpExp byteType LShift args
mkExp (SOp LB8LShr args) = return $ mkBinOpExp byteType RRShift args
mkExp (SOp LB8AShr args) = return $ mkBinOpExp byteType RShift args
mkExp (SOp LB8And args) = return $ mkBinOpExp byteType And args
mkExp (SOp LB8Or args) = return $ mkBinOpExp byteType Or args
mkExp (SOp LB8Xor args) = return $ mkBinOpExp byteType Xor args
mkExp (SOp LB8Compl [var]) = 
  return $ PreBitCompl (mkVarAccess (Just $ byteType) var)
mkExp (SOp LB8Z16 [var]) = return $ mkZeroExt "shortValue" 8 byteType shortType var
mkExp (SOp LB8Z32 [var]) = return $ mkZeroExt "intValue" 8 byteType integerType var
mkExp (SOp LB8Z64 [var]) = return $ mkZeroExt "longValue" 8 byteType longType var
mkExp (SOp LB8S16 [var]) = return $ mkSignedExt "shortValue" byteType shortType var
mkExp (SOp LB8S32 [var]) = return $ mkSignedExt "intValue" byteType integerType var
mkExp (SOp LB8S64 [var]) = return $ mkSignedExt "longValue" byteType longType var
mkExp (SOp LB16Lt args) = return $ mkLogicalBinOpExp shortType LThan args
mkExp (SOp LB16Lte args) = return $ mkLogicalBinOpExp shortType LThanE args
mkExp (SOp LB16Eq args) = 
  return $ mkMethodOpChain1 (mkBoolToNumber shortType) shortType "equals" args
mkExp (SOp LB16Gt args) = return $ mkLogicalBinOpExp shortType GThan args
mkExp (SOp LB16Gte args) = return $ mkLogicalBinOpExp shortType GThanE args
mkExp (SOp LB16Plus args) = return $ mkBinOpExp shortType Add args
mkExp (SOp LB16Minus args) = return $ mkBinOpExp shortType Sub args
mkExp (SOp LB16Times args) = return $ mkBinOpExp shortType Mult args
mkExp (SOp LB16UDiv args) = return $ mkBinOpExpConv "intValue" IntT shortType Div args
mkExp (SOp LB16SDiv args) = return $ mkBinOpExp shortType Div args
mkExp (SOp LB16URem args) = return $ mkBinOpExpConv "intValue" IntT shortType Rem args
mkExp (SOp LB16SRem args) = return $ mkBinOpExp shortType Rem args
mkExp (SOp LB16Shl args) = return $ mkBinOpExp shortType LShift args
mkExp (SOp LB16LShr args) = return $ mkBinOpExp shortType RRShift args
mkExp (SOp LB16AShr args) = return $ mkBinOpExp shortType RShift args
mkExp (SOp LB16And args) = return $ mkBinOpExp shortType And args
mkExp (SOp LB16Or args) = return $ mkBinOpExp shortType Or args
mkExp (SOp LB16Xor args) = return $ mkBinOpExp shortType Xor args
mkExp (SOp LB16Compl [var]) = 
  return $ PreBitCompl (mkVarAccess (Just $ shortType) var)
mkExp (SOp LB16Z32 [var]) = return $ mkZeroExt "intValue" 16 shortType integerType var
mkExp (SOp LB16Z64 [var]) = return $ mkZeroExt "longValue" 16 shortType longType var
mkExp (SOp LB16S32 [var]) = return $ mkSignedExt "intValue" shortType integerType var
mkExp (SOp LB16S64 [var]) = return $ mkSignedExt "longValue" shortType longType var
mkExp (SOp LB16T8 [var]) = 
  return . MethodInv $ 
         TypeMethodCall (J.Name [Ident "Byte"])
                        []
                        (Ident "valueOf")
                        [ MethodInv $ PrimaryMethodCall (mkVarAccess (Just $ shortType) var) [] (Ident "byteValue") [] ]
mkExp (SOp LB32Lt args) = return $ mkLogicalBinOpExp integerType LThan args
mkExp (SOp LB32Lte args) = return $ mkLogicalBinOpExp integerType LThanE args
mkExp (SOp LB32Eq args) = 
  return $ mkMethodOpChain1 (mkBoolToNumber integerType) integerType "equals" args
mkExp (SOp LB32Gt args) = return $ mkLogicalBinOpExp integerType GThan args
mkExp (SOp LB32Gte args) = return $ mkLogicalBinOpExp integerType GThanE args
mkExp (SOp LB32Plus args) = return $ mkBinOpExp integerType Add args
mkExp (SOp LB32Minus args) = return $ mkBinOpExp integerType Sub args
mkExp (SOp LB32Times args) = return $ mkBinOpExp integerType Mult args
mkExp (SOp LB32UDiv args) = return $ mkBinOpExpConv "longValue" LongT integerType Div args
mkExp (SOp LB32SDiv args) = return $ mkBinOpExp integerType Div args
mkExp (SOp LB32URem args) = return $ mkBinOpExpConv "longValue" LongT integerType Rem args
mkExp (SOp LB32SRem args) = return $ mkBinOpExp integerType Rem args
mkExp (SOp LB32Shl args) = return $ mkBinOpExp integerType LShift args
mkExp (SOp LB32LShr args) = return $ mkBinOpExp integerType RRShift args
mkExp (SOp LB32AShr args) = return $ mkBinOpExp integerType RShift args
mkExp (SOp LB32And args) = return $ mkBinOpExp integerType And args
mkExp (SOp LB32Or args) = return $ mkBinOpExp integerType Or args
mkExp (SOp LB32Xor args) = return $ mkBinOpExp integerType Xor args
mkExp (SOp LB32Compl [var]) = 
  return $ PreBitCompl (mkVarAccess (Just $ integerType) var)
mkExp (SOp LB32Z64 [var]) = return $ mkZeroExt "longValue" 32 integerType longType var
mkExp (SOp LB32S64 [var]) = return $ mkSignedExt "longValue" integerType longType var
mkExp (SOp LB32T8 [var]) = 
  return . MethodInv $ 
         TypeMethodCall (J.Name [Ident "Byte"])
                        []
                        (Ident "valueOf")
                        [ MethodInv $ PrimaryMethodCall (mkVarAccess (Just $ integerType) var) [] (Ident "byteValue") [] ]
mkExp (SOp LB32T16 [var]) = 
  return . MethodInv $ 
         TypeMethodCall (J.Name [Ident "Short"])
                        []
                        (Ident "valueOf")
                        [ MethodInv $ PrimaryMethodCall (mkVarAccess (Just $ integerType) var) [] (Ident "shortValue") [] ]
mkExp (SOp LB64Lt args) = return $ mkLogicalBinOpExp longType LThan args
mkExp (SOp LB64Lte args) = return $ mkLogicalBinOpExp longType LThanE args
mkExp (SOp LB64Eq args) = 
  return $ mkMethodOpChain1 (mkBoolToNumber longType) longType "equals" args
mkExp (SOp LB64Gt args) = return $ mkLogicalBinOpExp longType GThan args
mkExp (SOp LB64Gte args) = return $ mkLogicalBinOpExp longType GThanE args
mkExp (SOp LB64Plus args) = return $ mkBinOpExp longType Add args
mkExp (SOp LB64Minus args) = return $ mkBinOpExp longType Sub args
mkExp (SOp LB64Times args) = return $ mkBinOpExp longType Mult args
mkExp (SOp LB64UDiv (arg:args)) = 
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
                                                                         [ (mkVarAccess (Just longType) arg) ]
                                            ]
                              )
                              []
                              (Ident "longValue")
                              []
                 )                                
           (mkVarAccess (Just longType) arg)
           args
mkExp (SOp LB64SDiv args) = return $ mkBinOpExp longType Div args
mkExp (SOp LB64URem (arg:args)) =
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
                                                                         [ (mkVarAccess (Just longType) arg) ]
                                            ]
                              )
                              []
                              (Ident "longValue")
                              []
                 )                                
           (mkVarAccess (Just longType) arg)
           args
mkExp (SOp LB64SRem args) = return $ mkBinOpExp longType Rem args
mkExp (SOp LB64Shl args) = return $ mkBinOpExp longType LShift args
mkExp (SOp LB64LShr args) = return $ mkBinOpExp longType RRShift args
mkExp (SOp LB64AShr args) = return $ mkBinOpExp longType RShift args
mkExp (SOp LB64And args) = return $ mkBinOpExp longType And args
mkExp (SOp LB64Or args) = return $ mkBinOpExp longType Or args
mkExp (SOp LB64Xor args) = return $ mkBinOpExp longType Xor args
mkExp (SOp LB64Compl [var]) = 
  return $ PreBitCompl (mkVarAccess (Just $ longType) var)
mkExp (SOp LB64T8 [var]) = 
  return . MethodInv $ 
         TypeMethodCall (J.Name [Ident "Byte"])
                        []
                        (Ident "valueOf")
                        [ MethodInv $ PrimaryMethodCall (mkVarAccess (Just $ longType) var) [] (Ident "byteValue") [] ]
mkExp (SOp LB64T16 [var]) = 
  return . MethodInv $ 
         TypeMethodCall (J.Name [Ident "Short"])
                        []
                        (Ident "valueOf")
                        [ MethodInv $ PrimaryMethodCall (mkVarAccess (Just $ longType) var) [] (Ident "shortValue") [] ]
mkExp (SOp LB64T32 [var]) = 
  return . MethodInv $ 
         TypeMethodCall (J.Name [Ident "Integer"])
                        []
                        (Ident "valueOf")
                        [ MethodInv $ PrimaryMethodCall (mkVarAccess (Just $ longType) var) [] (Ident "intValue") [] ]
mkExp (SOp LIntB8 [arg]) = mkExp (SOp LB32T8 [arg])
mkExp (SOp LIntB16 [arg]) = mkExp (SOp LB32T16 [arg])
mkExp (SOp LIntB32 [arg]) = mkExp (SV arg)
mkExp (SOp LIntB64 [arg]) = mkExp (SOp LB32S64 [arg])
mkExp (SOp LB32Int [arg]) = mkExp (SV arg)
mkExp (SOp LFExp [arg]) = return $ mkMathFun "exp" arg
mkExp (SOp LFLog [arg]) = return $ mkMathFun "log" arg
mkExp (SOp LFSin [arg]) = return $ mkMathFun "sin" arg
mkExp (SOp LFCos [arg]) = return $ mkMathFun "cos" arg
mkExp (SOp LFTan [arg]) = return $ mkMathFun "tan" arg
mkExp (SOp LFASin [arg]) = return $ mkMathFun "asin" arg
mkExp (SOp LFACos [arg]) = return $ mkMathFun "acos" arg
mkExp (SOp LFATan [arg]) = return $ mkMathFun "atan" arg
mkExp (SOp LFSqrt [arg]) = return $ mkMathFun "sqrt" arg
mkExp (SOp LFFloor [arg]) = return $ mkMathFun "floor" arg
mkExp (SOp LFCeil [arg]) = return $ mkMathFun "ceil" arg
mkExp (SOp LStrHead [arg]) = return $ mkStringAtIndex arg (Lit $ Int 0)
mkExp (SOp LStrTail [arg]) = 
  return . MethodInv $ PrimaryMethodCall (mkVarAccess (Just stringType) arg)
                                         []
                                         (Ident "substring")
                                         [Lit $ Int 1]
mkExp (SOp LStrCons [c, cs]) =
  return . MethodInv $ 
         PrimaryMethodCall ( MethodInv $ PrimaryMethodCall (InstanceCreation [] 
                                                                             (ClassType [(Ident "StringBuilder", [])])
                                                                             [mkVarAccess (Just stringType) cs]
                                                                             Nothing
                                                           )
                                                           []
                                                           (Ident "insert")
                                                           [ Lit $ Int 0, 
                                                             Cast (PrimType CharT) 
                                                                  (MethodInv $ PrimaryMethodCall 
                                                                               (mkVarAccess (Just integerType) c)
                                                                               []
                                                                               (Ident "intValue")
                                                                               []
                                                                  )
                                                           ]
                           )
                           []
                           (Ident "toString")
                           []
mkExp (SOp LStrIndex [str, i]) = return $ mkStringAtIndex str (mkVarAccess (Just integerType) i)
mkExp (SOp LStrRev [str]) = 
  return . MethodInv $ 
         PrimaryMethodCall ( MethodInv $ PrimaryMethodCall (InstanceCreation []
                                                                            (ClassType [(Ident "StringBuffer", [])])
                                                                            [mkVarAccess (Just stringType) str]
                                                                            Nothing
                                                           )
                                                           []
                                                           (Ident "reverse")
                                                           []
                           )
                           []
                           (Ident "toString")
                           []
mkExp (SOp LStdIn []) = return $ mkSystemStd In
mkExp (SOp LStdOut []) = return $ mkSystemStd Out
mkExp (SOp LStdErr []) = return $ mkSystemStd Err
mkExp (SOp LFork [arg]) = mkThread arg
mkExp (SOp LPar [arg]) = mkExp (SV arg)
mkExp (SOp LVMPtr []) = 
  return . MethodInv $ TypeMethodCall (J.Name [Ident "Thread"]) [] (Ident "currentThread") []
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