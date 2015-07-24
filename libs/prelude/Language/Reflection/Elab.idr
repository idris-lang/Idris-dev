||| Primitives and tactics for elaborator reflection.
|||
||| Elaborator reflection allows Idris code to control Idris's
||| built-in elaborator, and re-use features like the unifier, the
||| type checker, and the hole mechanism.
module Language.Reflection.Elab

import Builtins
import Prelude.Applicative
import Prelude.Bool
import Prelude.Functor
import Prelude.List
import Prelude.Maybe
import Prelude.Monad
import Language.Reflection

||| Erasure annotations reflect Idris's idea of what is intended to be
||| erased.
data Erasure = Erased | NotErased

||| How an argument is provided in high-level Idris
data Plicity =
  ||| The argument is directly provided at the application site
  Explicit |
  ||| The argument is found by Idris at the application site
  Implicit |
  ||| The argument is solved using type class resolution
  Constraint

||| Function arguments
|||
||| These are the simplest representation of argument lists, and are
||| used for functions.
record FunArg where
  constructor MkFunArg
  argName : TTName
  argTy   : Raw
  plicity : Plicity
  erasure : Erasure

||| Type constructor arguments
|||
||| Each argument is identified as being either a parameter that is
||| consistent in all constructors, or an index that varies based on
||| which constructor is selected.
data TyConArg =
  ||| Parameters are uniform across the constructors
  TyConParameter FunArg |
  ||| Indices are not uniform
  TyConIndex FunArg

||| A type declaration
data TyDecl : Type where
  ||| A type declaration.
  |||
  ||| Each argument is in the scope of the names of previous
  ||| arguments, and the return type is in the scope of all the
  ||| argument names.
  |||
  ||| @ fn the name to be declared, fully-qualified
  ||| @ args the arguments to the function
  ||| @ ret the final return type
  Declare : (fn : TTName) -> (args : List FunArg) -> (ret : Raw) -> TyDecl

||| A single pattern-matching clause
data FunClause : Type where
  MkFunClause : (lhs, rhs : Raw) -> FunClause

||| A reflected function definition.
data FunDefn : Type where
  DefineFun : TTName -> List FunClause -> FunDefn


data CtorArg = CtorParameter FunArg | CtorField FunArg

||| A reflected datatype definition
record Datatype where
  constructor MkDatatype

  ||| The name of the type constructor
  familyName : TTName

  ||| The arguments to the type constructor
  tyConArgs : List TyConArg

  ||| The result of the type constructor
  tyConRes : Raw

  ||| The constructors for the family
  constructors : List (TTName, List CtorArg, Raw)

||| A reflected elaboration script.
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

  prim__Check : Raw -> Elab (TT, TT)

  prim__SourceLocation : Elab SourceLocation
  prim__Namespace : Elab (List String)

  prim__Forget : TT -> Elab Raw

  prim__Gensym : String -> Elab TTName

  prim__Solve : Elab ()
  prim__Fill : Raw -> Elab ()
  prim__Apply : Raw -> List (Bool, Int) -> Elab (List (TTName, TTName))
  prim__MatchApply : Raw -> List (Bool, Int) -> Elab (List (TTName, TTName))
  prim__Focus : TTName -> Elab ()
  prim__Unfocus : TTName -> Elab ()
  prim__Attack : Elab ()

  prim__Rewrite : Raw -> Elab ()

  prim__Claim : TTName -> Raw -> Elab ()
  prim__Intro : Maybe TTName -> Elab ()
  prim__Forall : TTName -> Raw -> Elab ()
  prim__PatVar : TTName -> Elab ()
  prim__PatBind : TTName -> Elab ()

  prim__Compute : Elab ()

  prim__DeclareType : TyDecl -> Elab ()
  prim__DefineFunction : FunDefn -> Elab ()
  prim__AddInstance : TTName -> TTName -> Elab ()

  prim__ResolveTC : TTName -> Elab ()
  prim__Search : Int -> List TTName -> Elab ()
  prim__RecursiveElab : Raw -> Elab () -> Elab (TT, TT)

  prim__Debug : {a : Type} -> List ErrorReportPart -> Elab a
  prim__Metavar : TTName -> Elab ()

-------------
-- Public API
-------------
%access public
namespace Tactics
  instance Functor Elab where
    map f t = prim__BindElab t (\x => prim__PureElab (f x))

  instance Applicative Elab where
    pure x  = prim__PureElab x
    f <*> x = prim__BindElab f $ \g =>
              prim__BindElab x $ \y =>
              prim__PureElab   $ g y

  ||| The Alternative instance on Elab represents left-biased error
  ||| handling. In other words, `t <|> t'` will run `t`, and if it
  ||| fails, roll back the elaboration state and run `t'`.
  instance Alternative Elab where
    empty   = prim__Fail [TextPart "empty"]
    x <|> y = prim__Try x y

  instance Monad Elab where
    x >>= f = prim__BindElab x f

  ||| Halt elaboration with an error
  fail : List ErrorReportPart -> Elab a
  fail err = prim__Fail err

  ||| Look up the lexical binding at the focused hole
  getEnv : Elab (List (TTName, Binder TT))
  getEnv = prim__Env

  ||| Get the name and type of the focused hole
  getGoal : Elab (TTName, TT)
  getGoal = prim__Goal

  ||| Get the hole queue, in order
  getHoles : Elab (List TTName)
  getHoles = prim__Holes

  ||| If the current hole contains a guess, return it
  getGuess : Elab (Maybe TT)
  getGuess = prim__Guess

  ||| Look up the types of every overloading of a name
  lookupTy :  TTName -> Elab (List (TTName, NameType, TT))
  lookupTy n = prim__LookupTy n

  ||| Get the type of a fully-qualified name
  lookupTyExact : TTName -> Elab (TTName, NameType, TT)
  lookupTyExact n = case !(lookupTy n) of
                      [res] => return res
                      []    => fail [NamePart n, TextPart "is not defined."]
                      xs    => fail [NamePart n, TextPart "is ambiguous."]

  ||| Find the reflected representation of all datatypes whose names
  ||| are overloadings of some name
  lookupDatatype : TTName -> Elab (List Datatype)
  lookupDatatype n = prim__LookupDatatype n

  ||| Find the reflected representation of a datatype, given its
  ||| fully-qualified name.
  lookupDatatypeExact : TTName -> Elab Datatype
  lookupDatatypeExact n = case !(lookupDatatype n) of
                            [res] => return res
                            []    => fail [TextPart "No datatype named", NamePart n]
                            xs    => fail [TextPart "More than one datatype named", NamePart n]

  ||| Attempt to type-check a term, getting back itself and its type
  check : (tm : Raw) -> Elab (TT, TT)
  check tm = prim__Check tm

  ||| Convert a type-annotated reflected term to its untyped
  ||| equivalent
  forgetTypes : TT -> Elab Raw
  forgetTypes tt = prim__Forget tt

  ||| Generate a unique name based on some hint.
  |||
  ||| **NB**: the generated name is unique _for this run of the
  ||| elaborator_. Do not assume that they are globally unique.
  gensym : (hint : String) -> Elab TTName
  gensym hint = prim__Gensym hint

  ||| Substitute a guess into a hole.
  solve : Elab ()
  solve = prim__Solve

  ||| Place a term into a hole, unifying its type
  fill : Raw -> Elab ()
  fill tm = prim__Fill tm

  ||| Attempt to apply an operator to fill the current hole,
  ||| potentially solving arugments by unification.
  |||
  ||| The return value is a list of pairs of names, one for each input
  ||| argument. The first projection of these pairs is the original
  ||| name of the argument, from the type declaration, and the second
  ||| projection is the hole into which it is placed.
  |||
  ||| Note that not all of the returned hole names still exist, as
  ||| they may have been solved.
  |||
  ||| @ op the term to apply
  |||
  ||| @ argSpec instructions for finding the arguments to the term,
  |||     where the Boolean states whether or not to attempt to solve
  |||     the argument and the Int gives the priority in which to do
  |||     so
  apply : (op : Raw) ->
          (argSpec : List (Bool, Int)) ->
          Elab (List (TTName, TTName))
  apply tm argSpec = prim__Apply tm argSpec

  ||| Attempt to apply an operator to fill the current hole,
  ||| potentially solving arugments by matching.
  |||
  ||| The return value is a list of pairs of names, one for each input
  ||| argument. The first projection of these pairs is the original
  ||| name of the argument, from the type declaration, and the second
  ||| projection is the hole into which it is placed.
  |||
  ||| Note that not all of the returned hole names still exist, as
  ||| they may have been solved.
  |||
  ||| @ op the term to apply
  |||
  ||| @ argSpec instructions for finding the arguments to the term,
  |||     where the Boolean states whether or not to attempt to solve
  |||     the argument and the Int gives the priority in which to do
  |||     so
  matchApply : (op : Raw) ->
               (argSpec : List (Bool, Int)) ->
               Elab (List (TTName, TTName))
  matchApply tm argSpec = prim__Apply tm argSpec

  ||| Move the focus to the specified hole
  |||
  ||| @ hole the hole to focus on
  focus : (hole : TTName) -> Elab ()
  focus hole = prim__Focus hole

  ||| Send the currently-focused hole to the end of the hole queue and
  ||| focus on the next hole.
  unfocus : TTName -> Elab ()
  unfocus hole = prim__Unfocus hole

  ||| Convert a hole to make it suitable for bindings.
  |||
  ||| The binding tactics require that a hole be directly under its
  ||| binding, or else the scopes of the generated terms won't make
  ||| sense. This tactic creates a new hole of the proper form, and
  ||| points the old hole at it.
  attack : Elab ()
  attack = prim__Attack

  ||| Introduce a new hole with a specified name and type.
  |||
  ||| The new hole will be focused, and the previously-focused hole
  ||| will be immediately after it in the hole queue.
  claim : TTName -> Raw -> Elab ()
  claim n ty = prim__Claim n ty

  ||| Introduce a lambda binding around the current hole and focus on
  ||| the body. Requires that the hole be in binding form (use
  ||| `attack`).
  |||
  ||| @ n the name to use for the argument, or `Nothing` to use the name
  |||   in the corresponding hole type (a dependent function)
  intro : (n : Maybe TTName) -> Elab ()
  intro n = prim__Intro n

  ||| Introduce a dependent function type binding into the current hole,
  ||| and focus on the body.
  forall : TTName -> Raw -> Elab ()
  forall n ty = prim__Forall n ty

  ||| Convert a hole into a pattern variable.
  patvar : TTName -> Elab ()
  patvar n = prim__PatVar n

  ||| Introduce a new pattern binding.
  patbind : TTName -> Elab ()
  patbind n = prim__PatBind n

  ||| Normalise the goal.
  compute : Elab ()
  compute = prim__Compute

  ||| Find the source context for the elaboration script
  getSourceLocation : Elab SourceLocation
  getSourceLocation = prim__SourceLocation

  ||| Attempt to solve the current goal with the source code location
  sourceLocation : Elab ()
  sourceLocation = do loc <- getSourceLocation
                      fill (quote loc)
                      solve

  ||| Get the current namespace at the point of tactic execution. This
  ||| allows scripts to define top-level names conveniently.
  |||
  ||| The namespace is represented as a reverse-order list of strings,
  ||| just as in the representation of names.
  currentNamespace : Elab (List String)
  currentNamespace = prim__Namespace

  ||| Attempt to rewrite the goal using an equality.
  |||
  ||| The tactic searches the goal for applicable subterms, and
  ||| constructs a context for `replace` using them. In some cases,
  ||| this is not possible, and `replace` must be called manually with
  ||| an appropriate context.
  rewriteWith : Raw -> Elab ()
  rewriteWith rule = prim__Rewrite rule

  ||| Add a type declaration to the global context.
  declareType : TyDecl -> Elab ()
  declareType decl = prim__DeclareType decl

  ||| Define a function in the global context. The function must have
  ||| already been declared, either in ordinary Idris code or using
  ||| `declareType`.
  defineFunction : FunDefn -> Elab ()
  defineFunction defun = prim__DefineFunction defun

  ||| Register a new instance for type class resolution
  |||
  ||| @ className the name of the class for which an instance is being registered
  ||| @ instName the name of the definition to use in instance search
  addInstance : (className, instName : TTName) -> Elab ()
  addInstance className instName = prim__AddInstance className instName

  ||| Attempt to solve the current goal with a type class dictionary
  |||
  ||| @ fn the name of the definition being elaborated (to prevent Idris
  ||| from looping)
  resolveTC : (fn : TTName) -> Elab ()
  resolveTC fn = prim__ResolveTC fn

  ||| Use Idris's internal proof search.
  search : Elab ()
  search = prim__Search 100 []

  ||| Use Idris's internal proof search, with more control.
  |||
  ||| @ depth the search depth
  ||| @ hints additional names to try
  search' : (depth : Int) -> (hints : List TTName) -> Elab ()
  search' depth hints = prim__Search depth hints

  ||| Halt elaboration, dumping the internal state for inspection.
  |||
  ||| This is intended for elaboration script developers, not for
  ||| end-users. Use `fail` for final scripts.
  debug : Elab a
  debug = prim__Debug []

  ||| Halt elaboration, dumping the internal state and displaying a
  ||| message.
  |||
  ||| This is intended for elaboration script developers, not for
  ||| end-users. Use `fail` for final scripts.
  |||
  ||| @ msg the message to display
  debugMessage : (msg : List ErrorReportPart) -> Elab a
  debugMessage msg = prim__Debug msg

  ||| Create a new top-level metavariable to solve the current hole.
  |||
  ||| @ name the name for the top-level variable
  metavar : (name : TTName) -> Elab ()
  metavar name = prim__Metavar name

  ||| Recursively invoke the reflected elaborator with some goal.
  |||
  ||| The result is the final term and its type.
  runElab : Raw -> Elab () -> Elab (TT, TT)
  runElab goal script = prim__RecursiveElab goal script

