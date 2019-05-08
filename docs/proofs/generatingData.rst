Generating Data and Functions at Compile Time
=============================================

We can  construct a data structure at compile-time in an Elab monad.
This can allow proofs to be generated for user defined types or it could allow types to be automatically generated to support user defined types.
An example is the code, from <a href="https://dl.acm.org/citation.cfm?id=2951932">Christensen-Brady joint paper</a> ('Elaborator Reflection: Extending Idris in Idris'), that automatically generates accessibility predicates using the Bove-Capretta method.
The following simple outline example is adapted from
`<https://github.com/idris-lang/Idris-dev/blob/master/test/meta002/DataDef.idr>`_

.. code-block:: idris

  module DataDef
  %language ElabReflection

  addData : Elab ()
  addData = do
    let dataname : TTName = `{{DataDef.N}}
    declareDatatype $ Declare dataname [MkFunArg `{{n}} `(Nat) Explicit NotErased] `(Type)
    defineDatatype $ DefineDatatype dataname [
        Constructor `{{MkN}} [MkFunArg `{{x}} `(Nat) Implicit NotErased]
            (RApp (Var `{{DataDef.N}}) (Var `{{x}})),
        Constructor `{{MkN'}} [MkFunArg `{{x}} `(Nat) Explicit NotErased]
            (RApp (Var `{{DataDef.N}}) (RApp (Var `{S}) (Var `{{x}})))
    ]

  %runElab addData

So this declares and defines the following data structure 'N' with a constructor 'MkN' which can have an implicit or an explicit Nat argument.

.. code-block:: idris

  data N : Nat -> Type where
    MkN : N x
    MkN' : (x : Nat) -> N (S x)

Which can be used like this:

.. code-block:: idris

  λΠ> :t N
  N : Nat -> Type
  λΠ> N 2
  N 2 : Type
  λΠ> N 0
  N 0 : Type
  λΠ> :t MkN
  MkN : N x

Here is another, more complicated, example from the same test file. This also creates a function.

.. code-block:: idris

  module DataDef
  %language ElabReflection

  mkU : Elab ()
  mkU = do
    let U = `{{DataDef.U}}
    let el = `{{DataDef.el}}
    declareDatatype $ Declare U [] `(Type)
    declareType $ Declare el [MkFunArg `{{code}} (Var U) Explicit NotErased] `(Type)
    defineDatatype $ DefineDatatype U [
      Constructor `{{Base}} [] (Var U),
      Constructor `{{Pi}}
        [MkFunArg `{{code}} (Var U) Explicit NotErased,
          MkFunArg `{{body}} `(~(RApp (Var el) (Var `{{code}})) -> ~(Var U)) Explicit NotErased]
        (Var U)
    ]
    defineFunction $ DefineFun el [
       MkFunClause (RBind `{{code}} (PVar (Var U))
           (RBind `{{body}} (PVar `(~(RApp (Var el) (Var `{{code}})) -> ~(Var U)))
             (RApp (Var el)
               (RApp (RApp (Var `{{DataDef.Pi}})
                    (Var `{{code}}))
                  (Var `{{body}})))))
        (RBind `{{code}} (PVar (Var U))
          (RBind `{{body}} (PVar `(~(RApp (Var el) (Var `{{code}})) -> ~(Var U)))
            (RBind `{{x}} (Pi (RApp (Var el) (Var `{{code}})) `(Type))
              (RApp (Var el) (RApp (Var `{{body}}) (Var `{{x}})))))),
      MkFunClause (RApp (Var el) (Var `{{DataDef.Base}})) `(Bool)
  ]

  %runElab mkU

This code generates the following data and function:

.. code-block:: idris

  data U : Type where
    Base : U
    Pi : (code : U) -> (el code -> U) -> U
    el : U -> Type
    el (Pi code body) = (x : el code) -> el (body x)
    el Base = Bool

.. list-table:: Usage

   * - We can then use U the data structure, like this:
     - examples

       .. code-block:: idris

         λΠ> :t U
         U : Type
         λΠ> :doc U
         No documentation for U
         λΠ> Base
         Base : U
         λΠ> DataDef.Pi
         Pi : (code : U) -> (el code -> U) -> U

   * - el is the function that has been defined:
     - examples

       .. code-block:: idris

         λΠ> :t el
         el : U -> Type
         λΠ> el Base
         Bool : Type

So these are the functions that we can use to create data and functions in the Elab monad:

.. list-table:: Generating Data and Functions
   :widths: 10 30
   :stub-columns: 1

   * - declareType
     - Add a type declaration to the global context.

       Signature:

       declareType : TyDecl -> Elab ()
   * - defineFunction
     - Define a function in the global context. The function must have already been declared, either in ordinary Idris code or using `declareType`.

       Signature:

       defineFunction : FunDefn Raw -> Elab ()

   * - declareDatatype
     - Declare a datatype in the global context. This step only establishes the type constructor; use `defineDatatype` to give it constructors.

       Signature:

       declareDatatype : TyDecl -> Elab ()

   * - defineDatatype
     - Signature:

       defineDatatype : DataDefn -> Elab ()

   * - addImplementation
     - Register a new implementation for interface resolution.

       - @ ifaceName the name of the interface for which an implementation is being registered
       - @ implName the name of the definition to use in implementation search

       Signature:

       addImplementation : (ifaceName, implName : TTName) -> Elab ()

   * - isTCName
     - Determine whether a name denotes an interface.

       @ name a name that might denote an interface.

       Signature:

       isTCName : (name : TTName) -> Elab Bool

The above functions use the following data/records:

.. list-table:: Generating Data and Functions data/records
   :widths: 10 30
   :stub-columns: 1

   * - Plicity
     - How an argument is provided in high-level Idris

       .. code-block:: idris

         data  Plicity=
           ||| The argument is directly provided at the application site
           Explicit |
           ||| The argument is found by Idris at the application site
           Implicit |
           ||| The argument is solved using interface resolution
           Constraint

   * - FunArg
     - Function arguments
 
       These are the simplest representation of argument lists, and are used for functions. Additionally, because a FunArg provides enough
       information to build an application, a generic type lookup of a top-level identifier will return its FunArgs, if applicable.

       .. code-block:: idris

         record FunArg where
           constructor MkFunArg
           name    : TTName
           type    : Raw
           plicity : Plicity
           erasure : Erasure

   * - TyConArg
     - Type constructor arguments

       Each argument is identified as being either a parameter that is

       consistent in all constructors, or an index that varies based on

       which constructor is selected.

       .. code-block:: idris

          data TyConArg =
            ||| Parameters are uniform across the constructors
            TyConParameter FunArg |
            ||| Indices are not uniform
            TyConIndex FunArg

   * - TyDecl
     - A type declaration for a function or datatype

       .. code-block:: idris

         record TyDecl where
           constructor Declare
           ||| The fully-qualified name of the function or datatype being declared.
           name : TTName
           ||| Each argument is in the scope of the names of previous arguments.
           arguments : List FunArg
           ||| The return type is in the scope of all the argument names.
           returnType : Raw

   * - FunClause
     - A single pattern-matching clause

       .. code-block:: idris

         data FunClause : Type -> Type where
           MkFunClause : (lhs, rhs : a) -> FunClause a
           MkImpossibleClause : (lhs : a) -> FunClause a

   * - FunDefn
     - A reflected function definition.

       .. code-block:: idris

         record FunDefn a where
           constructor DefineFun
           name : TTName
           clauses : List (FunClause a)

   * - ConstructorDefn
     - A constructor to be associated with a new datatype.

       .. code-block:: idris

         record ConstructorDefn where
           constructor Constructor
           ||| The name of the constructor. The name must _not_ be qualified -
           ||| that is, it should begin with the `UN` or `MN` constructors.
           name : TTName
           ||| The constructor arguments. Idris will infer which arguments are
           ||| datatype parameters.
           arguments : List FunArg
           ||| The specific type constructed by the constructor.
           returnType : Raw

   * - DataDefn
     - A definition of a datatype to be added during an elaboration script.

       .. code-block:: idris

         record DataDefn where
           constructor DefineDatatype
           ||| The name of the datatype being defined. It must be
           ||| fully-qualified, and it must have been previously declared as a
           ||| datatype.
           name : TTName

   * - CtorArg
     - CtorParameter

       .. code-block:: idris

         data CtorArg = CtorParameter FunArg | CtorField FunArg

   * - Datatype
     - A reflected datatype definition

       .. code-block:: idris

         record Datatype where
           constructor MkDatatype
           ||| The name of the type constructor
           name : TTName
           ||| The arguments to the type constructor
           tyConArgs : List TyConArg
           ||| The result of the type constructor
           tyConRes : Raw
           ||| The constructors for the family
           constructors : List (TTName, List CtorArg, Raw)</td>

