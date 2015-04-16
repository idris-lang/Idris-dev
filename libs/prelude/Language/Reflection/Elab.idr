module Language.Reflection.Elab

import Builtins
import Prelude.Applicative
import Prelude.Functor
import Prelude.List
import Prelude.Maybe
import Prelude.Monad
import Language.Reflection

data Arg : Type where
  Explicit : TTName -> Raw -> Arg
  Implicit : TTName -> Raw -> Arg
  Constraint : TTName -> Raw -> Arg

data TyDecl : Type where
  Declare : TTName -> List Arg -> Raw -> TyDecl

data FunClause : Type where
  MkFunClause : (lhs, rhs : Raw) -> FunClause
  MkImpossibleClause : (lhs : Raw) -> FunClause

data FunDefn : Type where
  DefineFun : TTName -> List FunClause -> FunDefn

data TyConArg : Type where
  Parameter : TTName -> Raw -> TyConArg
  Index : TTName -> Raw -> TyConArg

data Datatype : Type where
  MkDatatype : (familyName : TTName) ->
               (tyConArgs : List TyConArg) -> (tyConRes : Raw) ->
               (constrs : List (TTName, Raw)) ->
               Datatype

abstract
data Elab : Type -> Type where
  -- obligatory control stuff
  prim__PureElab : a -> Elab a
  prim__BindElab : {a, b : Type} -> Elab a -> (a -> Elab b) -> Elab b

  prim__Try : {a : Type} -> Elab a -> Elab a -> Elab a
  prim__Fail : {a : Type} -> List ErrorReportPart -> Elab a

  prim__Env : Elab (List (TTName, Binder TT))
  prim__Goal : Elab (TTName, TT)
  prim__Holes : Elab (List TTName)
  prim__Guess : Elab (Maybe TT)
  prim__LookupTy : TTName -> Elab (List (TTName, NameType, TT))
  prim__LookupDatatype : TTName -> Elab (List Datatype)

  prim__SourceLocation : Elab SourceLocation

  prim__Forget : TT -> Elab Raw

  prim__Gensym : String -> Elab TTName

  prim__Solve : Elab ()
  prim__Fill : Raw -> Elab ()
  prim__Focus : TTName -> Elab ()
  prim__Unfocus : TTName -> Elab ()
  prim__Attack : Elab ()

  prim__Rewrite : Raw -> Elab ()

  prim__Claim : TTName -> Raw -> Elab ()
  prim__Intro : Maybe TTName -> Elab ()

  prim__DeclareType : TyDecl -> Elab ()
  prim__DefineFunction : FunDefn -> Elab ()

  prim__Debug : {a : Type} -> Maybe String -> Elab a


-------------
-- Public API
-------------
%access public

instance Functor Elab where
  map f t = prim__BindElab t (\x => prim__PureElab (f x))

instance Applicative Elab where
  pure x  = prim__PureElab x
  f <*> x = prim__BindElab f $ \g =>
            prim__BindElab x $ \y =>
            prim__PureElab   $ g y

instance Alternative Elab where
  empty   = prim__Fail [TextPart "empty"]
  x <|> y = prim__Try x y

instance Monad Elab where
  x >>= f = prim__BindElab x f

fail : List ErrorReportPart -> Elab a
fail err = prim__Fail err

getEnv : Elab (List (TTName, Binder TT))
getEnv = prim__Env

getGoal : Elab (TTName, TT)
getGoal = prim__Goal

getHoles : Elab (List TTName)
getHoles = prim__Holes

getGuess : Elab (Maybe TT)
getGuess = prim__Guess

lookupTy :  TTName -> Elab (List (TTName, NameType, TT))
lookupTy n = prim__LookupTy n

lookupTyExact : TTName -> Elab (TTName, NameType, TT)
lookupTyExact n = case !(lookupTy n) of
                    [res] => return res
                    []    => fail [NamePart n, TextPart "is not defined."]
                    xs    => fail [NamePart n, TextPart "is ambiguous."]

lookupDatatype : TTName -> Elab (List Datatype)
lookupDatatype n = prim__LookupDatatype n

lookupDatatypeExact : TTName -> Elab Datatype
lookupDatatypeExact n = case !(lookupDatatype n) of
                          [res] => return res
                          []    => fail [TextPart "No datatype named", NamePart n]
                          xs    => fail [TextPart "More than one datatype named", NamePart n]

forgetTypes : TT -> Elab Raw
forgetTypes tt = prim__Forget tt

gensym : (hint : String) -> Elab TTName
gensym hint = prim__Gensym hint

solve : Elab ()
solve = prim__Solve

fill : Raw -> Elab ()
fill tm = prim__Fill tm

focus : (hole : TTName) -> Elab ()
focus hole = prim__Focus hole

unfocus : TTName -> Elab ()
unfocus hole = prim__Unfocus hole

attack : Elab ()
attack = prim__Attack

claim : TTName -> Raw -> Elab ()
claim n ty = prim__Claim n ty

intro : Maybe TTName -> Elab ()
intro n = prim__Intro n

||| Find out the present source context for the tactic script
getSourceLocation : Elab SourceLocation
getSourceLocation = prim__SourceLocation

||| Attempt to solve the current goal with the source code location
sourceLocation : Elab ()
sourceLocation = do loc <- getSourceLocation
                    fill (quote loc)
                    solve

rewriteWith : Raw -> Elab ()
rewriteWith rule = prim__Rewrite rule

declareType : TyDecl -> Elab ()
declareType decl = prim__DeclareType decl

defineFunction : FunDefn -> Elab ()
defineFunction defun = prim__DefineFunction defun

debug : Elab a
debug = prim__Debug Nothing

debugMessage : String -> Elab a
debugMessage msg = prim__Debug (Just msg)
