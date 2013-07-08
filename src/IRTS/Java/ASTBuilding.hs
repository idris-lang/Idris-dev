module IRTS.Java.ASTBuilding where

import           IRTS.Java.JTypes

import           Language.Java.Syntax hiding (Name)
import qualified Language.Java.Syntax as J

toClassType :: J.Type -> ClassType
toClassType (RefType (ClassRefType ct)) = ct
toClassType t = error $ "Not a class type: " ++ (show t)

toRefType :: J.Type -> RefType
toRefType (RefType rt) = rt
toRefType t = error $ "Not a ref type: " ++ (show t)

class InvocationTarget a where
  (~>) :: a -> String -> [Argument] -> Exp

instance InvocationTarget ClassType where
  (~>) (ClassType ts) method args =
    MethodInv $ TypeMethodCall
      (J.Name $ map fst ts)
      (concatMap (map fromActType . snd) ts)
      (Ident method)
      args
    where
      fromActType (ActualType refType) = refType

instance InvocationTarget Exp where
  (~>) exp method args =
    MethodInv $ PrimaryMethodCall
      exp
      []
      (Ident method)
      args

instance InvocationTarget J.Type where
  (~>) t method args = ((toClassType t) ~> method) args

class Callable a where
  call :: a -> [Argument] -> Exp

instance Callable String where
  call method args =
    MethodInv $ MethodCall (J.Name [Ident method]) args

instance Callable Ident where
  call method args =
    MethodInv $ MethodCall (J.Name [method]) args

instance Callable J.Name where
  call method args =
    MethodInv $ MethodCall method args

(<>) :: Type -> Exp -> Exp
(<>) = Cast

(@!) :: Exp -> Int -> ArrayIndex
(@!) target pos =
  ArrayIndex target (Lit $ Int (toInteger pos))

(@:=) :: ArrayIndex -> Exp -> Exp
(@:=) lhs rhs = Assign (ArrayLhs lhs) EqualA rhs

(~&&~) :: Exp -> Exp -> Exp
(~&&~) e1 e2 = BinOp e1 CAnd e2

(~==~) :: Exp -> Exp -> Exp
(~==~) e1 e2 = BinOp e1 Equal e2

addToBlock :: [BlockStmt] -> Exp -> [BlockStmt]
addToBlock blk exp = blk ++ [BlockStmt $ ExpStmt exp]

jName :: String -> J.Name
jName n = J.Name [Ident n]

jConst :: String -> Exp
jConst = ExpName . jName

jReturn :: Exp -> BlockStmt
jReturn = BlockStmt . Return . Just

jInt :: Int -> Exp
jInt = Lit . Int . toInteger

jString :: String -> Exp
jString = Lit . String

simpleMethod :: [Modifier] -> Maybe J.Type -> String -> [FormalParam] -> Block -> Decl
simpleMethod mods t name params body =
  MemberDecl $ MethodDecl
    mods
    []
    t
    (Ident $ name)
    params
    []
    (MethodBody . Just $ body)

declareFinalObjectArray :: Ident -> Maybe VarInit -> BlockStmt
declareFinalObjectArray name init =
  LocalVars [Final]
            (array objectType)
            [ VarDecl
                (VarDeclArray . VarId $ name)
                init
            ]

arrayInitExps :: [Exp] -> VarInit
arrayInitExps = InitArray . ArrayInit . map (InitExp)

extendWithNull :: [Exp] -> Int -> [Exp]
extendWithNull exps additionalZeros =
  exps ++ (replicate additionalZeros (Lit $ Null))

closure :: [Exp] -> Exp -> Exp
closure params body =
  InstanceCreation
    []
    (toClassType idrisClosureType)
    params
    (Just $ ClassBody
       [ simpleMethod
           [Public, Final] (Just objectType) "call" []
           (Block [jReturn body])
       ]
    )

bigInteger :: String -> Exp
bigInteger s =
  InstanceCreation
      []
      (toClassType bigIntegerType)
      [Lit $ String s]
      Nothing
