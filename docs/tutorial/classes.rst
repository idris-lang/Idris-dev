.. _sect-classes:

============
Type Classes
============

We often want to define functions which work across several different
data types. For example, we would like arithmetic operators to work on
``Int``, ``Integer`` and ``Float`` at the very least. We would like
``==`` to work on the majority of data types. We would like to be able
to display different types in a uniform way.

To achieve this, we use a feature which has proved to be effective in
Haskell, namely *type classes*. To define a type class, we provide a
collection of overloaded operations which describe the interface for
*instances* of that class. A simple example is the ``Show`` type
class, which is defined in the prelude and provides an interface for
converting values to ``String``:

.. code-block:: idris

    class Show a where
        show : a -> String

This generates a function of the following type (which we call a
*method* of the ``Show`` class):

.. code-block:: idris

    show : Show a => a -> String

We can read this as: “under the constraint that ``a`` is an instance
of ``Show``, take an input ``a`` and return a ``String``.” An instance
of a class is defined with an ``instance`` declaration, which provides
implementations of the function for a specific type. For example, the
``Show`` instance for ``Nat`` could be defined as:

.. code-block:: idris

    instance Show Nat where
        show Z = "Z"
        show (S k) = "s" ++ show k

::

    Idris> show (S (S (S Z)))
    "sssZ" : String

Only one instance of a class can be given for a type — instances may
not overlap. Instance declarations can themselves have constraints.
To help with resolution, the arguments of an instance must be
constructors (either data or type constructors), variables or
constants (i.e. you cannot give an instance for a function).  For
example, to define a ``Show`` instance for vectors, we need to know
that there is a ``Show`` instance for the element type, because we are
going to use it to convert each element to a ``String``:

.. code-block:: idris

    instance Show a => Show (Vect n a) where
        show xs = "[" ++ show' xs ++ "]" where
            show' : Vect n a -> String
            show' Nil        = ""
            show' (x :: Nil) = show x
            show' (x :: xs)  = show x ++ ", " ++ show' xs

Default Definitions
-------------------

The library defines an ``Eq`` class which provides an interface for
comparing values for equality or inequality, with instances for all of
the built-in types:

.. code-block:: idris

    class Eq a where
        (==) : a -> a -> Bool
        (/=) : a -> a -> Bool

To declare an instance of a type, we have to give definitions of all
of the methods. For example, for an instance of ``Eq`` for ``Nat``:

.. code-block:: idris

    instance Eq Nat where
        Z     == Z     = True
        (S x) == (S y) = x == y
        Z     == (S y) = False
        (S x) == Z     = False

        x /= y = not (x == y)

It is hard to imagine many cases where the ``/=`` method will be
anything other than the negation of the result of applying the ``==``
method. It is therefore convenient to give a default definition for
each method in the class declaration, in terms of the other method:

.. code-block:: idris

    class Eq a where
        (==) : a -> a -> Bool
        (/=) : a -> a -> Bool

        x /= y = not (x == y)
        x == y = not (x /= y)

A minimal complete definition of an ``Eq`` instance requires either
``==`` or ``/=`` to be defined, but does not require both. If a method
definition is missing, and there is a default definition for it, then
the default is used instead.

Extending Classes
-----------------

Classes can also be extended. A logical next step from an equality
relation ``Eq`` is to define an ordering relation ``Ord``. We can
define an ``Ord`` class which inherits methods from ``Eq`` as well as
defining some of its own:

.. code-block:: idris

    data Ordering = LT | EQ | GT

.. code-block:: idris

    class Eq a => Ord a where
        compare : a -> a -> Ordering

        (<) : a -> a -> Bool
        (>) : a -> a -> Bool
        (<=) : a -> a -> Bool
        (>=) : a -> a -> Bool
        max : a -> a -> a
        min : a -> a -> a

The ``Ord`` class allows us to compare two values and determine their
ordering. Only the ``compare`` method is required; every other method
has a default definition. Using this we can write functions such as
``sort``, a function which sorts a list into increasing order,
provided that the element type of the list is in the ``Ord`` class. We
give the constraints on the type variables left of the fat arrow
``=>``, and the function type to the right of the fat arrow:

.. code-block:: idris

    sort : Ord a => List a -> List a

Functions, classes and instances can have multiple
constraints. Multiple constaints are written in brackets in a comma
separated list, for example:

.. code-block:: idris

    sortAndShow : (Ord a, Show a) => List a -> String
    sortAndShow xs = show (sort xs)

Functors and Applicatives
-------------------------

So far, we have seen single parameter type classes, where the parameter
is of type ``Type``. In general, there can be any number (greater than
0) of parameters, and the parameters can have *any* type. If the type
of the parameter is not ``Type``, we need to give an explicit type
declaration. For example, the ``Functor`` class is defined in the
library:

.. code-block:: idris

    class Functor (f : Type -> Type) where
        map : (m : a -> b) -> f a -> f b

A functor allows a function to be applied across a structure, for
example to apply a function to every element in a ``List``:

.. code-block:: idris

    instance Functor List where
      map f []      = []
      map f (x::xs) = f x :: map f xs

::

    Idris> map (*2) [1..10]
    [2, 4, 6, 8, 10, 12, 14, 16, 18, 20] : List Integer

Having defined ``Functor``, we can define ``Applicative`` which
abstracts the notion of function application:

.. code-block:: idris

    infixl 2 <*>

    class Functor f => Applicative (f : Type -> Type) where
        pure  : a -> f a
        (<*>) : f (a -> b) -> f a -> f b

Monads and ``do``-notation
--------------------------

The ``Monad`` class allows us to encapsulate binding and computation,
and is the basis of ``do``-notation introduced in Section
:ref:`sect-do`. It extends ``Applicative`` as defined above, and is
defined as follows:

.. code-block:: idris

    class Applicative m => Monad (m : Type -> Type) where
        (>>=)  : m a -> (a -> m b) -> m b

Inside a ``do`` block, the following syntactic transformations are
applied:

- ``x <- v; e`` becomes ``v >>= (\backslashx => e)``

- ``v; e`` becomes ``v >>= (\backslash_ => e)``

- ``let x = v; e`` becomes ``let x = v in e``

``IO`` is an instance of ``Monad``, defined using primitive functions.
We can also define an instance for ``Maybe``, as follows:

.. code-block:: idris

    instance Monad Maybe where
        Nothing  >>= k = Nothing
        (Just x) >>= k = k x

Using this we can, for example, define a function which adds two
``Maybe Int``, using the monad to encapsulate the error handling:

.. code-block:: idris

    m_add : Maybe Int -> Maybe Int -> Maybe Int
    m_add x y = do x' <- x -- Extract value from x
                   y' <- y -- Extract value from y
                   return (x' + y') -- Add them

This function will extract the values from ``x`` and ``y``, if they
are available, or return ``Nothing`` if they are not. Managing the
``Nothing`` cases is achieved by the ``>>=`` operator, hidden by the
``do`` notation.

::

    *classes> m_add (Just 20) (Just 22)
    Just 42 : Maybe Int
    *classes> m_add (Just 20) Nothing
    Nothing : Maybe Int

``!``-notation
~~~~~~~~~~~~~~

In many cases, using ``do``-notation can make programs unnecessarily
verbose, particularly in cases such as ``m_add`` above where the value
bound is used once, immediately. In these cases, we can use a
shorthand version, as follows:

.. code-block:: idris

    m_add : Maybe Int -> Maybe Int -> Maybe Int
    m_add x y = return (!x + !y)

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
~~~~~~~~~~~~~~~~~~~~

The list comprehension notation we saw in Section
:ref:`sect-more-expr` is more general, and applies to anything which
is an instance of both ``Monad`` and ``Alternative``:

.. code-block:: idris

    class Applicative f => Alternative (f : Type -> Type) where
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

    do { qual1; qual2; ...; qualn; return exp; }

Using monad comprehensions, an alternative definition for ``m_add``
would be:

.. code-block:: idris

    m_add : Maybe Int -> Maybe Int -> Maybe Int
    m_add x y = [ x' + y' | x' <- x, y' <- y ]

Idiom brackets
--------------

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
application, we can use to do the job for us. To do this, we can make
``Maybe`` an instance of ``Applicative`` as follows, where ``<>`` is
defined in the same way as ``m_app`` above (this is defined in the
``Idris`` library):

.. code-block:: idris

    instance Applicative Maybe where
        pure = Just

        (Just f) <*> (Just a) = Just (f a)
        _        <*> _        = Nothing

Using we can use this instance as follows, where a function
application ``[| f a1 …an |]`` is translated into ``pure f <> a1 <>
…<> an``:

.. code-block:: idris

    m_add' : Maybe Int -> Maybe Int -> Maybe Int
    m_add' x y = [| x + y |]

An error-handling interpreter
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Idiom notation is commonly useful when defining evaluators. McBride
and Paterson describe such an evaluator [1]_, for a language similar
to the following:

.. code-block:: idris

    data Expr = Var String      -- variables
              | Val Int         -- values
              | Add Expr Expr   -- addition

Evaluation will take place relative to a context mapping variables
(represented as ``String``s) to integer values, and can possibly fail.
We define a data type ``Eval`` to wrap an evaluator:

.. code-block:: idris

    data Eval : Type -> Type where
         MkEval : (List (String, Int) -> Maybe a) -> Eval a

Wrapping the evaluator in a data type means we will be able to make it
an instance of a type class later. We begin by defining a function to
retrieve values from the context during evaluation:

.. code-block:: idris

    fetch : String -> Eval Int
    fetch x = MkEval (\e => fetchVal e) where
        fetchVal : List (String, Int) -> Maybe Int
        fetchVal [] = Nothing
        fetchVal ((v, val) :: xs) = if (x == v)
                                      then (Just val)
                                      else (fetchVal xs)

When defining an evaluator for the language, we will be applying
functions in the context of an ``Eval``, so it is natural to make
``Eval`` an instance of ``Applicative``. Before ``Eval`` can be an
instance of ``Applicative`` it is necessary to make ``Eval`` an
instance of ``Functor``:

.. code-block:: idris

    instance Functor Eval where
        map f (MkEval g) = MkEval (\e => map f (g e))

    instance Applicative Eval where
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

Named Instances
---------------

It can be desirable to have multiple instances of a type class, for
example to provide alternative methods for sorting or printing values.
To achieve this, instances can be *named* as follows:

.. code-block:: idris

    instance [myord] Ord Nat where
       compare Z (S n)     = GT
       compare (S n) Z     = LT
       compare Z Z         = EQ
       compare (S x) (S y) = compare @{myord} x y

This declares an instance as normal, but with an explicit name,
``myord``. The syntax ``compare @{myord}`` gives an explicit instance to
``compare``, otherwise it would use the default instance for ``Nat``. We
can use this, for example, to sort a list of ``Nat`` in reverse.
Given the following list:

.. code-block:: idris

    testList : List Nat
    testList = [3,4,1]

We can sort it using the default ``Ord`` instance, then the named
instance ``myord`` as follows, at the ``Idris`` prompt:

::

    *named_instance> show (sort testList)
    "[sO, sssO, ssssO]" : String
    *named_instance> show (sort @{myord} testList)
    "[ssssO, sssO, sO]" : String


Determining Parameters
----------------------

When a class has more than one parameter, it can help resolution if
the parameters used to resolve the type class are restricted. For
example:

.. code-block:: idris

    class Monad m => MonadState s (m : Type -> Type) | m where
      get : m s
      put : s -> m ()

In this class, only ``m`` needs to be known to resolve this class, and
``s`` can then be determined from the instance. This is declared with
the ``| m`` after the class declaration. We call ``m`` a *determining
parameter* of the ``MonadState`` class, because it is the parameter
used to resolve an instance.


.. [1] Conor Mcbride and Ross Paterson. 2008. Applicative programming
       with effects. J. Funct. Program. 18, 1 (January 2008),
       1-13. DOI=10.1017/S0956796807006326
       http://dx.doi.org/10.1017/S0956796807006326
