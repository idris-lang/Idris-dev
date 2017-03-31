.. _sect-interfaces:

**********
Interfaces
**********

We often want to define functions which work across several different
data types. For example, we would like arithmetic operators to work on
``Int``, ``Integer`` and ``Double`` at the very least. We would like
``==`` to work on the majority of data types. We would like to be able
to display different types in a uniform way.

To achieve this, we use *interfaces*, which are similar to type classes in
Haskell or traits in Rust.  To define an interface, we provide a collection of
overloadable functions.  A simple example is the ``Show``
interface, which is defined in the prelude and provides an interface for
converting values to ``String``:

.. code-block:: idris

    interface Show a where
        show : a -> String

This generates a function of the following type (which we call a
*method* of the ``Show`` interface):

.. code-block:: idris

    show : Show a => a -> String

We can read this as: “under the constraint that ``a`` has an implementation
of ``Show``, take an input ``a`` and return a ``String``.” An implementation
of an interface is defined by giving definitions of the methods of the interface.
For example, the
``Show`` implementation for ``Nat`` could be defined as:

.. code-block:: idris

    Show Nat where
        show Z = "Z"
        show (S k) = "s" ++ show k

::

    Idris> show (S (S (S Z)))
    "sssZ" : String

Only one implementation of an interface can be given for a type — implementations may
not overlap. Implementation declarations can themselves have constraints.
To help with resolution, the arguments of an implementation must be
constructors (either data or type constructors), variables or
constants (i.e. you cannot give an implementation for a function).  For
example, to define a ``Show`` implementation for vectors, we need to know
that there is a ``Show`` implementation for the element type, because we are
going to use it to convert each element to a ``String``:

.. code-block:: idris

    Show a => Show (Vect n a) where
        show xs = "[" ++ show' xs ++ "]" where
            show' : Vect n a -> String
            show' Nil        = ""
            show' (x :: Nil) = show x
            show' (x :: xs)  = show x ++ ", " ++ show' xs

Default Definitions
===================

The library defines an ``Eq`` interface which provides methods for
comparing values for equality or inequality, with implementations for all of
the built-in types:

.. code-block:: idris

    interface Eq a where
        (==) : a -> a -> Bool
        (/=) : a -> a -> Bool

To declare an implementation for a type, we have to give definitions of all
of the methods. For example, for an implementation of ``Eq`` for ``Nat``:

.. code-block:: idris

    Eq Nat where
        Z     == Z     = True
        (S x) == (S y) = x == y
        Z     == (S y) = False
        (S x) == Z     = False

        x /= y = not (x == y)

It is hard to imagine many cases where the ``/=`` method will be
anything other than the negation of the result of applying the ``==``
method. It is therefore convenient to give a default definition for
each method in the interface declaration, in terms of the other method:

.. code-block:: idris

    interface Eq a where
        (==) : a -> a -> Bool
        (/=) : a -> a -> Bool

        x /= y = not (x == y)
        x == y = not (x /= y)

A minimal complete implementation of ``Eq`` requires either
``==`` or ``/=`` to be defined, but does not require both. If a method
definition is missing, and there is a default definition for it, then
the default is used instead.

Extending Interfaces
====================

Interfaces can also be extended. A logical next step from an equality
relation ``Eq`` is to define an ordering relation ``Ord``. We can
define an ``Ord`` interface which inherits methods from ``Eq`` as well as
defining some of its own:

.. code-block:: idris

    data Ordering = LT | EQ | GT

.. code-block:: idris

    interface Eq a => Ord a where
        compare : a -> a -> Ordering

        (<) : a -> a -> Bool
        (>) : a -> a -> Bool
        (<=) : a -> a -> Bool
        (>=) : a -> a -> Bool
        max : a -> a -> a
        min : a -> a -> a

The ``Ord`` interface allows us to compare two values and determine their
ordering. Only the ``compare`` method is required; every other method
has a default definition. Using this we can write functions such as
``sort``, a function which sorts a list into increasing order,
provided that the element type of the list is in the ``Ord`` interface. We
give the constraints on the type variables left of the fat arrow
``=>``, and the function type to the right of the fat arrow:

.. code-block:: idris

    sort : Ord a => List a -> List a

Functions, interfaces and implementations can have multiple
constraints. Multiple constraints are written in brackets in a comma
separated list, for example:

.. code-block:: idris

    sortAndShow : (Ord a, Show a) => List a -> String
    sortAndShow xs = show (sort xs)

Note: Interfaces and ``mutual`` blocks
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Idris is strictly "define before use", except in ``mutual`` blocks.
In a ``mutual`` block, Idris elaborates in two passes: types on the first 
pass and definitions on the second. When the mutual block contains an
interface declaration, it elaborates the interface header but none of the
method types on the first pass, and elaborates the method types and any
default definitions on the second pass.

Functors and Applicatives
=========================

So far, we have seen single parameter interfaces, where the parameter
is of type ``Type``. In general, there can be any number of parameters
(even zero), and the parameters can have *any* type. If the type
of the parameter is not ``Type``, we need to give an explicit type
declaration. For example, the ``Functor`` interface is defined in the
prelude:

.. code-block:: idris

    interface Functor (f : Type -> Type) where
        map : (m : a -> b) -> f a -> f b

A functor allows a function to be applied across a structure, for
example to apply a function to every element in a ``List``:

.. code-block:: idris

    Functor List where
      map f []      = []
      map f (x::xs) = f x :: map f xs

::

    Idris> map (*2) [1..10]
    [2, 4, 6, 8, 10, 12, 14, 16, 18, 20] : List Integer

Having defined ``Functor``, we can define ``Applicative`` which
abstracts the notion of function application:

.. code-block:: idris

    infixl 2 <*>

    interface Functor f => Applicative (f : Type -> Type) where
        pure  : a -> f a
        (<*>) : f (a -> b) -> f a -> f b

.. _monadsdo:

Monads and ``do``-notation
==========================

The ``Monad`` interface allows us to encapsulate binding and computation,
and is the basis of ``do``-notation introduced in Section
:ref:`sect-do`. It extends ``Applicative`` as defined above, and is
defined as follows:

.. code-block:: idris

    interface Applicative m => Monad (m : Type -> Type) where
        (>>=)  : m a -> (a -> m b) -> m b

Inside a ``do`` block, the following syntactic transformations are
applied:

- ``x <- v; e`` becomes ``v >>= (\x => e)``

- ``v; e`` becomes ``v >>= (\_ => e)``

- ``let x = v; e`` becomes ``let x = v in e``

``IO`` has an implementation of ``Monad``, defined using primitive functions.
We can also define an implementation for ``Maybe``, as follows:

.. code-block:: idris

    Monad Maybe where
        Nothing  >>= k = Nothing
        (Just x) >>= k = k x

Using this we can, for example, define a function which adds two
``Maybe Int``, using the monad to encapsulate the error handling:

.. code-block:: idris

    m_add : Maybe Int -> Maybe Int -> Maybe Int
    m_add x y = do x' <- x -- Extract value from x
                   y' <- y -- Extract value from y
                   pure (x' + y') -- Add them

This function will extract the values from ``x`` and ``y``, if they
are both available, or return ``Nothing`` if one or both are not ("fail fast"). Managing the
``Nothing`` cases is achieved by the ``>>=`` operator, hidden by the
``do`` notation.

::

    *Interfaces> m_add (Just 20) (Just 22)
    Just 42 : Maybe Int
    *Interfaces> m_add (Just 20) Nothing
    Nothing : Maybe Int

Pattern Matching Bind
---------------------

Sometimes we want to pattern match immediately on the result of a function
in ``do`` notation. For example, let's say we have a function ``readNumber``
which reads a number from the console, returning a value of the form
``Just x`` if the number is valid, or ``Nothing`` otherwise:

.. code-block:: idris

    readNumber : IO (Maybe Nat)
    readNumber = do
      input <- getLine
      if all isDigit (unpack input)
         then pure (Just (cast input))
         else pure Nothing

If we then use it to write a function to read two numbers, returning
``Nothing`` if neither are valid, then we would like to pattern match
on the result of ``readNumber``:

.. code-block:: idris

    readNumbers : IO (Maybe (Nat, Nat))
    readNumbers =
      do x <- readNumber
         case x of
              Nothing => pure Nothing
              Just x_ok => do y <- readNumber
                              case y of
                                   Nothing => pure Nothing
                                   Just y_ok => pure (Just (x_ok, y_ok))

If there's a lot of error handling, this could get deeply nested very quickly!
So instead, we can combine the bind and the pattern match in one line. For example,
we could try pattern matching on values of the form ``Just x_ok``:

.. code-block:: idris

    readNumbers : IO (Maybe (Nat, Nat))
    readNumbers =
      do Just x_ok <- readNumber
         Just y_ok <- readNumber
         pure (Just (x_ok, y_ok))

There is still a problem, however, because we've now omitted the case for
``Nothing`` so ``readNumbers`` is no longer total! We can add the ``Nothing``
case back as follows:

.. code-block:: idris

    readNumbers : IO (Maybe (Nat, Nat))
    readNumbers =
      do Just x_ok <- readNumber | Nothing => pure Nothing
         Just y_ok <- readNumber | Nothing => pure Nothing
         pure (Just (x_ok, y_ok))

The effect of this version of ``readNumbers`` is identical to the first (in
fact, it is syntactic sugar for it and directly translated back into that form).
The first part of each statement (``Just x_ok <-`` and ``Just y_ok <-``) gives
the preferred binding - if this matches, execution will continue with the rest
of the ``do`` block. The second part gives the alternative bindings, of which
there may be more than one.

``!``-notation
--------------

In many cases, using ``do``-notation can make programs unnecessarily
verbose, particularly in cases such as ``m_add`` above where the value
bound is used once, immediately. In these cases, we can use a
shorthand version, as follows:

.. code-block:: idris

    m_add : Maybe Int -> Maybe Int -> Maybe Int
    m_add x y = pure (!x + !y)

The notation ``!expr`` means that the expression ``expr`` should be
evaluated and then implicitly bound. Conceptually, we can think of
``!`` as being a prefix function with the following type:

.. code-block:: idris

    (!) : m a -> a

Note, however, that it is not really a function, merely syntax! In
practice, a subexpression ``!expr`` will lift ``expr`` as high as
possible within its current scope, bind it to a fresh name ``x``, and
replace ``!expr`` with ``x``. Expressions are lifted depth first, left
to right. In practice, ``!``-notation allows us to program in a more
direct style, while still giving a notational clue as to which
expressions are monadic.

For example, the expression:

.. code-block:: idris

    let y = 42 in f !(g !(print y) !x)

is lifted to:

.. code-block:: idris

    let y = 42 in do y' <- print y
                     x' <- x
                     g' <- g y' x'
                     f g'

Monad comprehensions
--------------------

The list comprehension notation we saw in Section
:ref:`sect-more-expr` is more general, and applies to anything which
has an implementation of both ``Monad`` and ``Alternative``:

.. code-block:: idris

    interface Applicative f => Alternative (f : Type -> Type) where
        empty : f a
        (<|>) : f a -> f a -> f a

In general, a comprehension takes the form ``[ exp | qual1, qual2, …,
qualn ]`` where ``quali`` can be one of:

- A generator ``x <- e``

- A *guard*, which is an expression of type ``Bool``

- A let binding ``let x = e``

To translate a comprehension ``[exp | qual1, qual2, …, qualn]``, first
any qualifier ``qual`` which is a *guard* is translated to ``guard
qual``, using the following function:

.. code-block:: idris

    guard : Alternative f => Bool -> f ()

Then the comprehension is converted to ``do`` notation:

.. code-block:: idris

    do { qual1; qual2; ...; qualn; pure exp; }

Using monad comprehensions, an alternative definition for ``m_add``
would be:

.. code-block:: idris

    m_add : Maybe Int -> Maybe Int -> Maybe Int
    m_add x y = [ x' + y' | x' <- x, y' <- y ]

Idiom brackets
==============

While ``do`` notation gives an alternative meaning to sequencing,
idioms give an alternative meaning to *application*. The notation and
larger example in this section is inspired by Conor McBride and Ross
Paterson’s paper “Applicative Programming with Effects” [1]_.

First, let us revisit ``m_add`` above. All it is really doing is
applying an operator to two values extracted from ``Maybe Int``. We
could abstract out the application:

.. code-block:: idris

    m_app : Maybe (a -> b) -> Maybe a -> Maybe b
    m_app (Just f) (Just a) = Just (f a)
    m_app _        _        = Nothing

Using this, we can write an alternative ``m_add`` which uses this
alternative notion of function application, with explicit calls to
``m_app``:

.. code-block:: idris

    m_add' : Maybe Int -> Maybe Int -> Maybe Int
    m_add' x y = m_app (m_app (Just (+)) x) y

Rather than having to insert ``m_app`` everywhere there is an
application, we can use idiom brackets to do the job for us.
To do this, we can give ``Maybe`` an implementation of ``Applicative``
as follows, where ``<*>`` is defined in the same way as ``m_app``
above (this is defined in the Idris library):

.. code-block:: idris

    Applicative Maybe where
        pure = Just

        (Just f) <*> (Just a) = Just (f a)
        _        <*> _        = Nothing

Using ``<*>`` we can use this implementation as follows, where a function
application ``[| f a1 …an |]`` is translated into ``pure f <*> a1 <*>
… <*> an``:

.. code-block:: idris

    m_add' : Maybe Int -> Maybe Int -> Maybe Int
    m_add' x y = [| x + y |]

An error-handling interpreter
-----------------------------

Idiom notation is commonly useful when defining evaluators. McBride
and Paterson describe such an evaluator [1]_, for a language similar
to the following:

.. code-block:: idris

    data Expr = Var String      -- variables
              | Val Int         -- values
              | Add Expr Expr   -- addition

Evaluation will take place relative to a context mapping variables
(represented as ``String``\s) to ``Int`` values, and can possibly fail.
We define a data type ``Eval`` to wrap an evaluator:

.. code-block:: idris

    data Eval : Type -> Type where
         MkEval : (List (String, Int) -> Maybe a) -> Eval a

Wrapping the evaluator in a data type means we will be able to provide
implementations of interfaces for it later. We begin by defining a function to
retrieve values from the context during evaluation:

.. code-block:: idris

    fetch : String -> Eval Int
    fetch x = MkEval (\e => fetchVal e) where
        fetchVal : List (String, Int) -> Maybe Int
        fetchVal [] = Nothing
        fetchVal ((v, val) :: xs) = if (x == v)
                                      then (Just val)
                                      else (fetchVal xs)

When defining an evaluator for the language, we will be applying functions in
the context of an ``Eval``, so it is natural to give ``Eval`` an implementation
of ``Applicative``. Before ``Eval`` can have an implementation of
``Applicative`` it is necessary for ``Eval`` to have an implementation of
``Functor``:

.. code-block:: idris

    Functor Eval where
        map f (MkEval g) = MkEval (\e => map f (g e))

    Applicative Eval where
        pure x = MkEval (\e => Just x)

        (<*>) (MkEval f) (MkEval g) = MkEval (\x => app (f x) (g x)) where
            app : Maybe (a -> b) -> Maybe a -> Maybe b
            app (Just fx) (Just gx) = Just (fx gx)
            app _         _         = Nothing

Evaluating an expression can now make use of the idiomatic application
to handle errors:

.. code-block:: idris

    eval : Expr -> Eval Int
    eval (Var x)   = fetch x
    eval (Val x)   = [| x |]
    eval (Add x y) = [| eval x + eval y |]

    runEval : List (String, Int) -> Expr -> Maybe Int
    runEval env e = case eval e of
        MkEval envFn => envFn env

Named Implementations
=====================

It can be desirable to have multiple implementations of an interface for the
same type, for example to provide alternative methods for sorting or printing
values.  To achieve this, implementations can be *named* as follows:

.. code-block:: idris

    [myord] Ord Nat where
       compare Z (S n)     = GT
       compare (S n) Z     = LT
       compare Z Z         = EQ
       compare (S x) (S y) = compare @{myord} x y

This declares an implementation as normal, but with an explicit name,
``myord``. The syntax ``compare @{myord}`` gives an explicit implementation to
``compare``, otherwise it would use the default implementation for ``Nat``. We
can use this, for example, to sort a list of ``Nat`` in reverse.
Given the following list:

.. code-block:: idris

    testList : List Nat
    testList = [3,4,1]

We can sort it using the default ``Ord`` implementation, then the named
implementation ``myord`` as follows, at the Idris prompt:

::

    *named_impl> show (sort testList)
    "[sO, sssO, ssssO]" : String
    *named_impl> show (sort @{myord} testList)
    "[ssssO, sssO, sO]" : String


Sometimes, we also need access to a named parent implementation. For example,
the prelude defines the following ``Semigroup`` interface:

.. code-block:: idris

    interface Semigroup ty where
      (<+>) : ty -> ty -> ty

Then it defines ``Monoid``, which extends ``Semigroup`` with a "neutral"
value:

.. code-block:: idris

    interface Semigroup ty => Monoid ty where
      neutral : ty

We can define two different implementations of ``Semigroup`` and
``Monoid`` for ``Nat``, one based on addition and one on multiplication:

.. code-block:: idris

    [PlusNatSemi] Semigroup Nat where
      (<+>) x y = x + y

    [MultNatSemi] Semigroup Nat where
      (<+>) x y = x * y

The neutral value for addition is ``0``, but the neutral value for multiplication
is ``1``. It's important, therefore, that when we define implementations
of ``Monoid`` they extend the correct ``Semigroup`` implementation. We can
do this with a ``using`` clause in the implementation as follows:

.. code-block:: idris

    [PlusNatMonoid] Monoid Nat using PlusNatSemi where
      neutral = 0

    [MultNatMonoid] Monoid Nat using MultNatSemi where
      neutral = 1

The ``using PlusNatSemi`` clause indicates that ``PlusNatMonoid`` should
extend ``PlusNatSemi`` specifically.

Determining Parameters
======================

When an interface has more than one parameter, it can help resolution if the
parameters used to find an implementation are restricted. For example:

.. code-block:: idris

    interface Monad m => MonadState s (m : Type -> Type) | m where
      get : m s
      put : s -> m ()

In this interface, only ``m`` needs to be known to find an implementation of
this interface, and ``s`` can then be determined from the implementation. This
is declared with the ``| m`` after the interface declaration. We call ``m`` a
*determining parameter* of the ``MonadState`` interface, because it is the
parameter used to find an implementation.


.. [1] Conor McBride and Ross Paterson. 2008. Applicative programming
       with effects. J. Funct. Program. 18, 1 (January 2008),
       1-13. DOI=10.1017/S0956796807006326
       http://dx.doi.org/10.1017/S0956796807006326
