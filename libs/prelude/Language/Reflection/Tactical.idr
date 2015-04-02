module Language.Reflection.Tactical

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

data FunDefn : Type where
  DefineFun : TTName -> List FunClause -> FunDefn

abstract
data Tactical : Type -> Type where
  -- obligatory control stuff
  prim__PureTactical : a -> Tactical a
  prim__BindTactical : {a, b : Type} -> Tactical a -> (a -> Tactical b) -> Tactical b

  prim__Try : {a : Type} -> Tactical a -> Tactical a -> Tactical a
  prim__Fail : {a : Type} -> List ErrorReportPart -> Tactical a

  prim__Env : Tactical (List (TTName, Binder TT))
  prim__Goal : Tactical (TTName, TT)
  prim__Holes : Tactical (List TTName)
  prim__Guess : Tactical (Maybe TT)

  prim__SourceLocation : Tactical SourceLocation

  prim__Forget : TT -> Tactical Raw

  prim__Gensym : String -> Tactical TTName

  prim__Solve : Tactical ()
  prim__Fill : Raw -> Tactical ()
  prim__Focus : TTName -> Tactical ()
  prim__Unfocus : TTName -> Tactical ()
  prim__Attack : Tactical ()

  prim__Rewrite : Raw -> Tactical ()

  prim__Claim : TTName -> Raw -> Tactical ()
  prim__Intro : Maybe TTName -> Tactical ()

  prim__DeclareType : TyDecl -> Tactical ()
  prim__DefineFunction : FunDefn -> Tactical ()

  prim__Debug : {a : Type} -> Maybe String -> Tactical a


-------------
-- Public API
-------------
%access public

instance Functor Tactical where
  map f t = prim__BindTactical t (\x => prim__PureTactical (f x))

instance Applicative Tactical where
  pure x  = prim__PureTactical x
  f <*> x = prim__BindTactical f $ \g =>
            prim__BindTactical x $ \y =>
            prim__PureTactical   $ g y

instance Alternative Tactical where
  empty   = prim__Fail [TextPart "empty"]
  x <|> y = prim__Try x y

instance Monad Tactical where
  x >>= f = prim__BindTactical x f

fail : List ErrorReportPart -> Tactical a
fail err = prim__Fail err

getEnv : Tactical (List (TTName, Binder TT))
getEnv = prim__Env

getGoal : Tactical (TTName, TT)
getGoal = prim__Goal

getHoles : Tactical (List TTName)
getHoles = prim__Holes

getGuess : Tactical (Maybe TT)
getGuess = prim__Guess

forgetTypes : TT -> Tactical Raw
forgetTypes tt = prim__Forget tt

gensym : (hint : String) -> Tactical TTName
gensym hint = prim__Gensym hint

solve : Tactical ()
solve = prim__Solve

fill : Raw -> Tactical ()
fill tm = prim__Fill tm

focus : (hole : TTName) -> Tactical ()
focus hole = prim__Focus hole

unfocus : TTName -> Tactical ()
unfocus hole = prim__Unfocus hole

attack : Tactical ()
attack = prim__Attack

claim : TTName -> Raw -> Tactical ()
claim n ty = prim__Claim n ty

intro : Maybe TTName -> Tactical ()
intro n = prim__Intro n

||| Find out the present source context for the tactic script
getSourceLocation : Tactical SourceLocation
getSourceLocation = prim__SourceLocation

||| Attempt to solve the current goal with the source code location
sourceLocation : Tactical ()
sourceLocation = do loc <- getSourceLocation
                    fill (quote loc)
                    solve

rewriteWith : Raw -> Tactical ()
rewriteWith rule = prim__Rewrite rule

declareType : TyDecl -> Tactical ()
declareType decl = prim__DeclareType decl

defineFunction : FunDefn -> Tactical ()
defineFunction defun = prim__DefineFunction defun

debug : Tactical a
debug = prim__Debug Nothing

debugMessage : String -> Tactical a
debugMessage msg = prim__Debug (Just msg)
