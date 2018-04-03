.. _sect-interp:

***********************************
Example: The Well-Typed Interpreter
***********************************

In this section, we’ll use the features we’ve seen so far to write a
larger example, an interpreter for a simple functional programming
language, with variables, function application, binary operators and
an ``if...then...else`` construct. We will use the dependent type
system to ensure that any programs which can be represented are
well-typed.

Representing Languages
======================

First, let us define the types in the language. We have integers,
booleans, and functions, represented by ``Ty``:

.. code-block:: idris

    data Ty = TyInt | TyBool | TyFun Ty Ty

We can write a function to translate these representations to a concrete
Idris type — remember that types are first class, so can be
calculated just like any other value:

.. code-block:: idris

    interpTy : Ty -> Type
    interpTy TyInt       = Integer
    interpTy TyBool      = Bool
    interpTy (TyFun A T) = interpTy A -> interpTy T

We're going to define a representation of our language in such a way
that only well-typed programs can be represented. We'll index the
representations of expressions by their type, **and** the types of
local variables (the context). The context can be represented using
the ``Vect`` data type, and as it will be used regularly it will be
represented as an implicit argument. To do so we define everything in
a ``using`` block (keep in mind that everything after this point needs
to be indented so as to be inside the ``using`` block):

.. code-block:: idris

    using (G:Vect n Ty)

Expressions are indexed by the types of the local variables, and the type of
the expression itself:

.. code-block:: idris

    data Expr : Vect n Ty -> Ty -> Type

The full representation of expressions is:

.. code-block:: idris

    data HasType : (i : Fin n) -> Vect n Ty -> Ty -> Type where
        Stop : HasType FZ (t :: G) t
        Pop  : HasType k G t -> HasType (FS k) (u :: G) t

    data Expr : Vect n Ty -> Ty -> Type where
        Var : HasType i G t -> Expr G t
        Val : (x : Integer) -> Expr G TyInt
        Lam : Expr (a :: G) t -> Expr G (TyFun a t)
        App : Expr G (TyFun a t) -> Expr G a -> Expr G t
        Op  : (interpTy a -> interpTy b -> interpTy c) ->
              Expr G a -> Expr G b -> Expr G c
        If  : Expr G TyBool ->
              Lazy (Expr G a) ->
              Lazy (Expr G a) -> Expr G a

The code above makes use of the ``Vect`` and ``Fin`` types from the
Idris standard library. We import them because they are not provided
in the prelude:

.. code-block:: idris

    import Data.Vect
    import Data.Fin

Since expressions are indexed by their type, we can read the typing
rules of the language from the definitions of the constructors. Let us
look at each constructor in turn.

We use a nameless representation for variables — they are *de Bruijn
indexed*. Variables are represented by a proof of their membership in
the context, ``HasType i G T``, which is a proof that variable ``i``
in context ``G`` has type ``T``. This is defined as follows:

.. code-block:: idris

    data HasType : (i : Fin n) -> Vect n Ty -> Ty -> Type where
        Stop : HasType FZ (t :: G) t
        Pop  : HasType k G t -> HasType (FS k) (u :: G) t

We can treat *Stop* as a proof that the most recently defined variable
is well-typed, and *Pop n* as a proof that, if the ``n``\ th most
recently defined variable is well-typed, so is the ``n+1``\ th. In
practice, this means we use ``Stop`` to refer to the most recently
defined variable, ``Pop Stop`` to refer to the next, and so on, via
the ``Var`` constructor:

.. code-block:: idris

    Var : HasType i G t -> Expr G t

So, in an expression ``\x. \y. x y``, the variable ``x`` would have a
de Bruijn index of 1, represented as ``Pop Stop``, and ``y 0``,
represented as ``Stop``. We find these by counting the number of
lambdas between the definition and the use.

A value carries a concrete representation of an integer:

.. code-block:: idris

    Val : (x : Integer) -> Expr G TyInt

A lambda creates a function. In the scope of a function of type ``a ->
t``, there is a new local variable of type ``a``, which is expressed
by the context index:

.. code-block:: idris

    Lam : Expr (a :: G) t -> Expr G (TyFun a t)

Function application produces a value of type ``t`` given a function
from ``a`` to ``t`` and a value of type ``a``:

.. code-block:: idris

    App : Expr G (TyFun a t) -> Expr G a -> Expr G t

We allow arbitrary binary operators, where the type of the operator
informs what the types of the arguments must be:

.. code-block:: idris

    Op : (interpTy a -> interpTy b -> interpTy c) ->
         Expr G a -> Expr G b -> Expr G c

Finally, ``If`` expressions make a choice given a boolean. Each branch
must have the same type, and we will evaluate the branches lazily so
that only the branch which is taken need be evaluated:

.. code-block:: idris

    If : Expr G TyBool ->
         Lazy (Expr G a) ->
         Lazy (Expr G a) ->
         Expr G a

Writing the Interpreter
=======================

When we evaluate an ``Expr``, we'll need to know the values in scope,
as well as their types. ``Env`` is an environment, indexed over the
types in scope. Since an environment is just another form of list,
albeit with a strongly specified connection to the vector of local
variable types, we use the usual ``::`` and ``Nil`` constructors so
that we can use the usual list syntax. Given a proof that a variable
is defined in the context, we can then produce a value from the
environment:

.. code-block:: idris

    data Env : Vect n Ty -> Type where
        Nil  : Env Nil
        (::) : interpTy a -> Env G -> Env (a :: G)

    lookup : HasType i G t -> Env G -> interpTy t
    lookup Stop    (x :: xs) = x
    lookup (Pop k) (x :: xs) = lookup k xs

Given this, an interpreter is a function which
translates an ``Expr`` into a concrete Idris value with respect to a
specific environment:

.. code-block:: idris

    interp : Env G -> Expr G t -> interpTy t

The complete interpreter is defined as follows, for reference. For
each constructor, we translate it into the corresponding Idris value:

.. code-block:: idris

    interp env (Var i)     = lookup i env
    interp env (Val x)     = x
    interp env (Lam sc)    = \x => interp (x :: env) sc
    interp env (App f s)   = interp env f (interp env s)
    interp env (Op op x y) = op (interp env x) (interp env y)
    interp env (If x t e)  = if interp env x then interp env t
                                             else interp env e

Let us look at each case in turn. To translate a variable, we simply look it
up in the environment:

.. code-block:: idris

    interp env (Var i) = lookup i env

To translate a value, we just return the concrete representation of the
value:

.. code-block:: idris

    interp env (Val x) = x

Lambdas are more interesting. In this case, we construct a function
which interprets the scope of the lambda with a new value in the
environment. So, a function in the object language is translated to an
Idris function:

.. code-block:: idris

    interp env (Lam sc) = \x => interp (x :: env) sc

For an application, we interpret the function and its argument and apply
it directly. We know that interpreting ``f`` must produce a function,
because of its type:

.. code-block:: idris

    interp env (App f s) = interp env f (interp env s)

Operators and conditionals are, again, direct translations into the
equivalent Idris constructs. For operators, we apply the function to
its operands directly, and for ``If``, we apply the Idris
``if...then...else`` construct directly.

.. code-block:: idris

    interp env (Op op x y) = op (interp env x) (interp env y)
    interp env (If x t e)  = if interp env x then interp env t
                                             else interp env e

Testing
=======

We can make some simple test functions. Firstly, adding two inputs
``\x. \y. y + x`` is written as follows:

.. code-block:: idris

    add : Expr G (TyFun TyInt (TyFun TyInt TyInt))
    add = Lam (Lam (Op (+) (Var Stop) (Var (Pop Stop))))

More interestingly, a factorial function ``fact``
(e.g. ``\x. if (x == 0) then 1 else (fact (x-1) * x)``),
can be written as:

.. code-block:: idris

    fact : Expr G (TyFun TyInt TyInt)
    fact = Lam (If (Op (==) (Var Stop) (Val 0))
                   (Val 1)
                   (Op (*) (App fact (Op (-) (Var Stop) (Val 1)))
                           (Var Stop)))

Running
=======

To finish, we write a ``main`` program which interprets the factorial
function on user input:

.. code-block:: idris

    main : IO ()
    main = do putStr "Enter a number: "
              x <- getLine
              printLn (interp [] fact (cast x))

Here, ``cast`` is an overloaded function which converts a value from
one type to another if possible. Here, it converts a string to an
integer, giving 0 if the input is invalid. An example run of this
program at the Idris interactive environment is:


.. _factrun:
.. literalinclude:: ../listing/idris-prompt-interp.txt


Aside: ``cast``
---------------

The prelude defines an interface ``Cast`` which allows conversion
between types:

.. code-block:: idris

    interface Cast from to where
        cast : from -> to

It is a *multi-parameter* interface, defining the source type and
object type of the cast. It must be possible for the type checker to
infer *both* parameters at the point where the cast is applied. There
are casts defined between all of the primitive types, as far as they
make sense.
