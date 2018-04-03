.. _sect-typefuns:

*******************
Types and Functions
*******************

Primitive Types
===============

Idris defines several primitive types: ``Int``, ``Integer`` and
``Double`` for numeric operations, ``Char`` and ``String`` for text
manipulation, and ``Ptr`` which represents foreign pointers. There are
also several data types declared in the library, including ``Bool``,
with values ``True`` and ``False``. We can declare some constants with
these types. Enter the following into a file ``Prims.idr`` and load it
into the Idris interactive environment by typing ``idris Prims.idr``:

.. code-block:: idris

    module Prims

    x : Int
    x = 42

    foo : String
    foo = "Sausage machine"

    bar : Char
    bar = 'Z'

    quux : Bool
    quux = False

An Idris file consists of an optional module declaration (here
``module Prims``) followed by an optional list of imports and a
collection of declarations and definitions. In this example no imports
have been specified. However Idris programs can consist of several
modules and the definitions in each module each have their own
namespace. This is discussed further in Section
:ref:`sect-namespaces`. When writing Idris programs both the order in which
definitions are given and indentation are significant. Functions and
data types must be defined before use, incidentally each definition must
have a type declaration, for example see ``x : Int``, ``foo :
String``, from the above listing. New declarations must begin at the
same level of indentation as the preceding declaration.
Alternatively, a semicolon ``;`` can be used to terminate declarations.

A library module ``prelude`` is automatically imported by every
Idris program, including facilities for IO, arithmetic, data
structures and various common functions. The prelude defines several
arithmetic and comparison operators, which we can use at the prompt.
Evaluating things at the prompt gives an answer, and the type of the
answer. For example:

::

    *prims> 6*6+6
    42 : Integer
    *prims> x == 6*6+6
    True : Bool

All of the usual arithmetic and comparison operators are defined for
the primitive types. They are overloaded using interfaces, as we
will discuss in Section :ref:`sect-interfaces` and can be extended to
work on user defined types. Boolean expressions can be tested with the
``if...then...else`` construct, for example:

::

    *prims> if x == 6 * 6 + 6 then "The answer!" else "Not the answer"
    "The answer!" : String

Data Types
==========

Data types are declared in a similar way and with similar syntax to
Haskell. Natural numbers and lists, for example, can be declared as
follows:

.. code-block:: idris

    data Nat    = Z   | S Nat           -- Natural numbers
                                        -- (zero and successor)
    data List a = Nil | (::) a (List a) -- Polymorphic lists

The above declarations are taken from the standard library. Unary
natural numbers can be either zero (``Z``), or the successor of
another natural number (``S k``). Lists can either be empty (``Nil``)
or a value added to the front of another list (``x :: xs``). In the
declaration for ``List``, we used an infix operator ``::``. New
operators such as this can be added using a fixity declaration, as
follows:

::

    infixr 10 ::

Functions, data constructors and type constructors may all be given
infix operators as names. They may be used in prefix form if enclosed
in brackets, e.g. ``(::)``. Infix operators can use any of the
symbols:

::

    :+-*\/=.?|&><!@$%^~#

Some operators built from these symbols can't be user defined. These are
``:``,  ``=>``,  ``->``,  ``<-``,  ``=``,  ``?=``,  ``|``,  ``**``,
``==>``,  ``\``,  ``%``,  ``~``,  ``?``,  and ``!``.

Functions
=========

Functions are implemented by pattern matching, again using a similar
syntax to Haskell. The main difference is that Idris requires type
declarations for all functions, using a single colon ``:`` (rather
than Haskell’s double colon ``::``). Some natural number arithmetic
functions can be defined as follows, again taken from the standard
library:

.. code-block:: idris

    -- Unary addition
    plus : Nat -> Nat -> Nat
    plus Z     y = y
    plus (S k) y = S (plus k y)

    -- Unary multiplication
    mult : Nat -> Nat -> Nat
    mult Z     y = Z
    mult (S k) y = plus y (mult k y)

The standard arithmetic operators ``+`` and ``*`` are also overloaded
for use by ``Nat``, and are implemented using the above functions.
Unlike Haskell, there is no restriction on whether types and function
names must begin with a capital letter or not. Function names
(``plus`` and ``mult`` above), data constructors (``Z``, ``S``,
``Nil`` and ``::``) and type constructors (``Nat`` and ``List``) are
all part of the same namespace. By convention, however,
data types and constructor names typically begin with a capital letter.
We can test these functions at the Idris prompt:

::

    Idris> plus (S (S Z)) (S (S Z))
    4 : Nat
    Idris> mult (S (S (S Z))) (plus (S (S Z)) (S (S Z)))
    12 : Nat

.. note::

   When displaying an element of ``Nat`` such as ``(S (S (S (S Z))))``,
   Idris displays it as ``4``.
   The result of ``plus (S (S Z)) (S (S Z))``
   is actually ``(S (S (S (S Z))))``
   which is the natural number ``4``.
   This can be checked at the Idris prompt:

::

    Idris> (S (S (S (S Z))))
    4 : Nat

Like arithmetic operations, integer literals are also overloaded using
interfaces, meaning that we can also test the functions as follows:

::

    Idris> plus 2 2
    4 : Nat
    Idris> mult 3 (plus 2 2)
    12 : Nat

You may wonder, by the way, why we have unary natural numbers when our
computers have perfectly good integer arithmetic built in. The reason
is primarily that unary numbers have a very convenient structure which
is easy to reason about, and easy to relate to other data structures
as we will see later. Nevertheless, we do not want this convenience to
be at the expense of efficiency. Fortunately, Idris knows about
the relationship between ``Nat`` (and similarly structured types) and
numbers. This means it can optimise the representation, and functions
such as ``plus`` and ``mult``.

``where`` clauses
-----------------

Functions can also be defined *locally* using ``where`` clauses. For
example, to define a function which reverses a list, we can use an
auxiliary function which accumulates the new, reversed list, and which
does not need to be visible globally:

.. code-block:: idris

    reverse : List a -> List a
    reverse xs = revAcc [] xs where
      revAcc : List a -> List a -> List a
      revAcc acc [] = acc
      revAcc acc (x :: xs) = revAcc (x :: acc) xs

Indentation is significant — functions in the ``where`` block must be
indented further than the outer function.

.. note:: Scope

    Any names which are visible in the outer scope are also visible in
    the ``where`` clause (unless they have been redefined, such as ``xs``
    here). A name which appears only in the type will be in scope in the
    ``where`` clause if it is a *parameter* to one of the types, i.e. it
    is fixed across the entire structure.

As well as functions, ``where`` blocks can include local data
declarations, such as the following where ``MyLT`` is not accessible
outside the definition of ``foo``:

.. code-block:: idris

    foo : Int -> Int
    foo x = case isLT of
                Yes => x*2
                No => x*4
        where
           data MyLT = Yes | No

           isLT : MyLT
           isLT = if x < 20 then Yes else No

In general, functions defined in a ``where`` clause need a type
declaration just like any top level function. However, the type
declaration for a function ``f`` *can* be omitted if:

- ``f`` appears in the right hand side of the top level definition

- The type of ``f`` can be completely determined from its first application


So, for example, the following definitions are legal:

.. code-block:: idris

    even : Nat -> Bool
    even Z = True
    even (S k) = odd k where
      odd Z = False
      odd (S k) = even k

    test : List Nat
    test = [c (S 1), c Z, d (S Z)]
      where c x = 42 + x
            d y = c (y + 1 + z y)
                  where z w = y + w

.. _sect-holes:

Holes
-----

Idris programs can contain *holes* which stand for incomplete parts of
programs. For example, we could leave a hole for the greeting in our
"Hello world" program:

.. code-block:: idris

    main : IO ()
    main = putStrLn ?greeting

The syntax ``?greeting`` introduces a hole, which stands for a part of
a program which is not yet written. This is a valid Idris program, and you
can check the type of ``greeting``:

::

    *Hello> :t greeting
    --------------------------------------
    greeting : String

Checking the type of a hole also shows the types of any variables in scope.
For example, given an incomplete definition of ``even``:

.. code-block:: idris

    even : Nat -> Bool
    even Z = True
    even (S k) = ?even_rhs

We can check the type of ``even_rhs`` and see the expected return type,
and the type of the variable ``k``:

::

    *Even> :t even_rhs
      k : Nat
    --------------------------------------
    even_rhs : Bool

Holes are useful because they help us write functions *incrementally*.
Rather than writing an entire function in one go, we can leave some parts
unwritten and use Idris to tell us what is necessary to complete the
definition.

Dependent Types
===============

.. _sect-fctypes:

First Class Types
-----------------

In Idris, types are first class, meaning that they can be computed and
manipulated (and passed to functions) just like any other language construct.
For example, we could write a function which computes a type:

.. code-block:: idris

    isSingleton : Bool -> Type
    isSingleton True = Nat
    isSingleton False = List Nat

This function calculates the appropriate type from a ``Bool`` which flags
whether the type should be a singleton or not. We can use this function
to calculate a type anywhere that a type can be used. For example, it
can be used to calculate a return type:

.. code-block:: idris

    mkSingle : (x : Bool) -> isSingleton x
    mkSingle True = 0
    mkSingle False = []

Or it can be used to have varying input types. The following function
calculates either the sum of a list of ``Nat``, or returns the given
``Nat``, depending on whether the singleton flag is true:

.. code-block:: idris

    sum : (single : Bool) -> isSingleton single -> Nat
    sum True x = x
    sum False [] = 0
    sum False (x :: xs) = x + sum False xs

Vectors
-------

A standard example of a dependent data type is the type of “lists with
length”, conventionally called vectors in the dependent type
literature. They are available as part of the Idris library, by
importing ``Data.Vect``, or we can declare them as follows:

.. code-block:: idris

    data Vect : Nat -> Type -> Type where
       Nil  : Vect Z a
       (::) : a -> Vect k a -> Vect (S k) a

Note that we have used the same constructor names as for ``List``.
Ad-hoc name overloading such as this is accepted by Idris,
provided that the names are declared in different namespaces (in
practice, normally in different modules). Ambiguous constructor names
can normally be resolved from context.

This declares a family of types, and so the form of the declaration is
rather different from the simple type declarations above. We
explicitly state the type of the type constructor ``Vect`` — it takes
a ``Nat`` and a type as an argument, where ``Type`` stands for the
type of types. We say that ``Vect`` is *indexed* over ``Nat`` and
*parameterised* by ``Type``. Each constructor targets a different part
of the family of types. ``Nil`` can only be used to construct vectors
with zero length, and ``::`` to construct vectors with non-zero
length. In the type of ``::``, we state explicitly that an element of
type ``a`` and a tail of type ``Vect k a`` (i.e., a vector of length
``k``) combine to make a vector of length ``S k``.

We can define functions on dependent types such as ``Vect`` in the same
way as on simple types such as ``List`` and ``Nat`` above, by pattern
matching. The type of a function over ``Vect`` will describe what
happens to the lengths of the vectors involved. For example, ``++``,
defined as follows, appends two ``Vect``:

.. code-block:: idris

    (++) : Vect n a -> Vect m a -> Vect (n + m) a
    (++) Nil       ys = ys
    (++) (x :: xs) ys = x :: xs ++ ys

The type of ``(++)`` states that the resulting vector’s length will be
the sum of the input lengths. If we get the definition wrong in such a
way that this does not hold, Idris will not accept the definition.
For example:

.. code-block:: idris

    (++) : Vect n a -> Vect m a -> Vect (n + m) a
    (++) Nil       ys = ys
    (++) (x :: xs) ys = x :: xs ++ xs -- BROKEN

When run through the Idris type checker, this results in the
following:

::

    $ idris VBroken.idr --check
    VBroken.idr:9:23-25:
    When checking right hand side of Vect.++ with expected type
            Vect (S k + m) a

    When checking an application of constructor Vect.:::
            Type mismatch between
                    Vect (k + k) a (Type of xs ++ xs)
            and
                    Vect (plus k m) a (Expected type)

            Specifically:
                    Type mismatch between
                            plus k k
                    and
                            plus k m


This error message suggests that there is a length mismatch between
two vectors — we needed a vector of length ``k + m``, but provided a
vector of length ``k + k``.

The Finite Sets
---------------

Finite sets, as the name suggests, are sets with a finite number of
elements. They are available as part of the Idris library, by
importing ``Data.Fin``, or can be declared as follows:

.. code-block:: idris

    data Fin : Nat -> Type where
       FZ : Fin (S k)
       FS : Fin k -> Fin (S k)

From the signature,  we can see that this is a type constructor that takes a ``Nat``, and produces a type.
So this is not a set in the sense of a collection that is a container of objects,
rather it is the canonical set of unnamed elements, as in "the set of 5 elements," for example.
Effectively, it is a type that captures integers that fall into the range of zero to ``(n - 1)`` where
``n`` is the argument used to instantiate the ``Fin`` type.
For example, ``Fin 5`` can be thought of as the type of integers between 0 and 4.

Let us look at the constructors in greater detail.

``FZ`` is the zeroth element of a finite set with ``S k`` elements;
``FS n`` is the ``n+1``\ th element of a finite set with ``S k``
elements. ``Fin`` is indexed by a ``Nat``, which represents the number
of elements in the set. Since we can’t construct an element of an
empty set, neither constructor targets ``Fin Z``.

As mentioned above, a useful application of the ``Fin`` family is to
represent bounded natural numbers. Since the first ``n`` natural
numbers form a finite set of ``n`` elements, we can treat ``Fin n`` as
the set of integers greater than or equal to zero and less than ``n``.

For example, the following function which looks up an element in a
``Vect``, by a bounded index given as a ``Fin n``, is defined in the
prelude:

.. code-block:: idris

    index : Fin n -> Vect n a -> a
    index FZ     (x :: xs) = x
    index (FS k) (x :: xs) = index k xs

This function looks up a value at a given location in a vector. The
location is bounded by the length of the vector (``n`` in each case),
so there is no need for a run-time bounds check. The type checker
guarantees that the location is no larger than the length of the
vector, and of course no less than zero.

Note also that there is no case for ``Nil`` here. This is because it
is impossible. Since there is no element of ``Fin Z``, and the
location is a ``Fin n``, then ``n`` can not be ``Z``. As a result,
attempting to look up an element in an empty vector would give a
compile time type error, since it would force ``n`` to be ``Z``.

Implicit Arguments
------------------

Let us take a closer look at the type of ``index``:

.. code-block:: idris

    index : Fin n -> Vect n a -> a

It takes two arguments, an element of the finite set of ``n`` elements,
and a vector with ``n`` elements of type ``a``. But there are also two
names, ``n`` and ``a``, which are not declared explicitly. These are
*implicit* arguments to ``index``. We could also write the type of
``index`` as:

.. code-block:: idris

    index : {a:Type} -> {n:Nat} -> Fin n -> Vect n a -> a

Implicit arguments, given in braces ``{}`` in the type declaration,
are not given in applications of ``index``; their values can be
inferred from the types of the ``Fin n`` and ``Vect n a``
arguments. Any name beginning with a lower case letter which appears
as a parameter or index in a
type declaration, which is not applied to any arguments, will
*always* be automatically
bound as an implicit argument. Implicit arguments can still be given
explicitly in applications, using ``{a=value}`` and ``{n=value}``, for
example:

.. code-block:: idris

    index {a=Int} {n=2} FZ (2 :: 3 :: Nil)

In fact, any argument, implicit or explicit, may be given a name. We
could have declared the type of ``index`` as:

.. code-block:: idris

    index : (i:Fin n) -> (xs:Vect n a) -> a

It is a matter of taste whether you want to do this — sometimes it can
help document a function by making the purpose of an argument more
clear.

Furthermore, ``{}`` can be used to pattern match on the left hand side, i.e.
``{var = pat}`` gets an implicit variable and attempts to pattern match on “pat”;
For example:

.. code-block:: idris

    isEmpty : Vect n a -> Bool
    isEmpty {n = Z} _   = True
    isEmpty {n = S k} _ = False

“``using``” notation
--------------------

Sometimes it is useful to provide types of implicit arguments,
particularly where there is a dependency ordering, or where the
implicit arguments themselves have dependencies. For example, we may
wish to state the types of the implicit arguments in the following
definition, which defines a predicate on vectors (this is also defined
in ``Data.Vect``, under the name ``Elem``):

.. code-block:: idris

    data IsElem : a -> Vect n a -> Type where
       Here :  {x:a} ->   {xs:Vect n a} -> IsElem x (x :: xs)
       There : {x,y:a} -> {xs:Vect n a} -> IsElem x xs -> IsElem x (y :: xs)

An instance of ``IsElem x xs`` states that ``x`` is an element of
``xs``.  We can construct such a predicate if the required element is
``Here``, at the head of the vector, or ``There``, in the tail of the
vector. For example:

.. code-block:: idris

    testVec : Vect 4 Int
    testVec = 3 :: 4 :: 5 :: 6 :: Nil

    inVect : IsElem 5 Main.testVec
    inVect = There (There Here)

.. important:: Implicit Arguments and Scope

    Within the type signature the typechecker will treat all variables
    that start with an lowercase letter **and** are not applied to
    something else as an implicit variable. To get the above code
    example to compile you will need to provide a qualified name for
    ``testVec``. In the example above, we have assumed that the code
    lives within the ``Main`` module.

If the same implicit arguments are being used a lot, it can make a
definition difficult to read. To avoid this problem, a ``using`` block
gives the types and ordering of any implicit arguments which can
appear within the block:

.. code-block:: idris

    using (x:a, y:a, xs:Vect n a)
      data IsElem : a -> Vect n a -> Type where
         Here  : IsElem x (x :: xs)
         There : IsElem x xs -> IsElem x (y :: xs)

Note: Declaration Order and ``mutual`` blocks
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

In general, functions and data types must be defined before use, since
dependent types allow functions to appear as part of types, and type
checking can rely on how particular functions are defined (though this
is only true of total functions; see Section :ref:`sect-totality`).
However, this restriction can be relaxed by using a ``mutual`` block,
which allows data types and functions to be defined simultaneously:

.. code-block:: idris

    mutual
      even : Nat -> Bool
      even Z = True
      even (S k) = odd k

      odd : Nat -> Bool
      odd Z = False
      odd (S k) = even k

In a ``mutual`` block, first all of the type declarations are added,
then the function bodies. As a result, none of the function types can
depend on the reduction behaviour of any of the functions in the
block.

I/O
===

Computer programs are of little use if they do not interact with the
user or the system in some way. The difficulty in a pure language such
as Idris — that is, a language where expressions do not have
side-effects — is that I/O is inherently side-effecting. Therefore in
Idris, such interactions are encapsulated in the type ``IO``:

.. code-block:: idris

    data IO a -- IO operation returning a value of type a

We’ll leave the definition of ``IO`` abstract, but effectively it
describes what the I/O operations to be executed are, rather than how
to execute them. The resulting operations are executed externally, by
the run-time system. We’ve already seen one IO program:

.. code-block:: idris

    main : IO ()
    main = putStrLn "Hello world"

The type of ``putStrLn`` explains that it takes a string, and returns
an element of the unit type ``()`` via an I/O action. There is a
variant ``putStr`` which outputs a string without a newline:

.. code-block:: idris

    putStrLn : String -> IO ()
    putStr   : String -> IO ()

We can also read strings from user input:

.. code-block:: idris

    getLine : IO String

A number of other I/O operations are defined in the prelude, for
example for reading and writing files, including:

.. code-block:: idris

    data File -- abstract
    data Mode = Read | Write | ReadWrite

    openFile : (f : String) -> (m : Mode) -> IO (Either FileError File)
    closeFile : File -> IO ()

    fGetLine : (h : File) -> IO (Either FileError String)
    fPutStr : (h : File) -> (str : String) -> IO (Either FileError ())
    fEOF : File -> IO Bool

Note that several of these return ``Either``, since they may fail.

.. _sect-do:

“``do``” notation
=================

I/O programs will typically need to sequence actions, feeding the
output of one computation into the input of the next. ``IO`` is an
abstract type, however, so we can’t access the result of a computation
directly. Instead, we sequence operations with ``do`` notation:

.. code-block:: idris

    greet : IO ()
    greet = do putStr "What is your name? "
               name <- getLine
               putStrLn ("Hello " ++ name)

The syntax ``x <- iovalue`` executes the I/O operation ``iovalue``, of
type ``IO a``, and puts the result, of type ``a`` into the variable
``x``. In this case, ``getLine`` returns an ``IO String``, so ``name``
has type ``String``. Indentation is significant — each statement in
the do block must begin in the same column. The ``pure`` operation
allows us to inject a value directly into an IO operation:

.. code-block:: idris

    pure : a -> IO a

As we will see later, ``do`` notation is more general than this, and
can be overloaded.

.. _sect-lazy:

Laziness
========

Normally, arguments to functions are evaluated before the function
itself (that is, Idris uses *eager* evaluation). However, this is
not always the best approach. Consider the following function:

.. code-block:: idris

    ifThenElse : Bool -> a -> a -> a
    ifThenElse True  t e = t
    ifThenElse False t e = e

This function uses one of the ``t`` or ``e`` arguments, but not both
(in fact, this is used to implement the ``if...then...else`` construct
as we will see later). We would prefer if *only* the argument which was
used was evaluated. To achieve this, Idris provides a ``Lazy``
data type, which allows evaluation to be suspended:

.. code-block:: idris

    data Lazy : Type -> Type where
         Delay : (val : a) -> Lazy a

    Force : Lazy a -> a

A value of type ``Lazy a`` is unevaluated until it is forced by
``Force``. The Idris type checker knows about the ``Lazy`` type,
and inserts conversions where necessary between ``Lazy a`` and ``a``,
and vice versa. We can therefore write ``ifThenElse`` as follows,
without any explicit use of ``Force`` or ``Delay``:

.. code-block:: idris

    ifThenElse : Bool -> Lazy a -> Lazy a -> a
    ifThenElse True  t e = t
    ifThenElse False t e = e

Codata Types
============

Codata types allow us to define infinite data structures by marking recursive
arguments as potentially infinite. For
a codata type ``T``, each of its constructor arguments of type ``T`` are transformed
into an argument of type ``Inf T``. This makes each of the ``T`` arguments
lazy, and allows infinite data structures of type ``T`` to be built. One
example of a codata type is Stream, which is defined as follows.

.. code-block:: idris

    codata Stream : Type -> Type where
      (::) : (e : a) -> Stream a -> Stream a

This gets translated into the following by the compiler.

.. code-block:: idris

    data Stream : Type -> Type where
      (::) : (e : a) -> Inf (Stream a) -> Stream a

The following is an example of how the codata type ``Stream`` can be used to
form an infinite data structure. In this case we are creating an infinite stream
of ones.

.. code-block:: idris

    ones : Stream Nat
    ones = 1 :: ones

It is important to note that codata does not allow the creation of infinite
mutually recursive data structures. For example the following will create an
infinite loop and cause a stack overflow.

.. code-block:: idris

    mutual
      codata Blue a = B a (Red a)
      codata Red a = R a (Blue a)

    mutual
      blue : Blue Nat
      blue = B 1 red

      red : Red Nat
      red = R 1 blue

    mutual
      findB : (a -> Bool) -> Blue a -> a
      findB f (B x r) = if f x then x else findR f r

      findR : (a -> Bool) -> Red a -> a
      findR f (R x b) = if f x then x else findB f b

    main : IO ()
    main = do printLn $ findB (== 1) blue

To fix this we must add explicit ``Inf`` declarations to the constructor
parameter types, since codata will not add it to constructor parameters of a
**different** type from the one being defined. For example, the following
outputs ``1``.

.. code-block:: idris

    mutual
      data Blue : Type -> Type where
       B : a -> Inf (Red a) -> Blue a

      data Red : Type -> Type where
       R : a -> Inf (Blue a) -> Red a

    mutual
      blue : Blue Nat
      blue = B 1 red

      red : Red Nat
      red = R 1 blue

    mutual
      findB : (a -> Bool) -> Blue a -> a
      findB f (B x r) = if f x then x else findR f r

      findR : (a -> Bool) -> Red a -> a
      findR f (R x b) = if f x then x else findB f b

    main : IO ()
    main = do printLn $ findB (== 1) blue

Useful Data Types
=================

Idris includes a number of useful data types and library functions
(see the ``libs/`` directory in the distribution, and the
`documentation <https://www.idris-lang.org/documentation/>`_). This section
describes a few of these. The functions described here are imported
automatically by every Idris program, as part of ``Prelude.idr``.

``List`` and ``Vect``
---------------------

We have already seen the ``List`` and ``Vect`` data types:

.. code-block:: idris

    data List a = Nil | (::) a (List a)

    data Vect : Nat -> Type -> Type where
       Nil  : Vect Z a
       (::) : a -> Vect k a -> Vect (S k) a

Note that the constructor names are the same for each — constructor
names (in fact, names in general) can be overloaded, provided that
they are declared in different namespaces (see Section
:ref:`sect-namespaces`), and will typically be resolved according to
their type. As syntactic sugar, any type with the constructor names
``Nil`` and ``::`` can be written in list form. For example:

-  ``[]`` means ``Nil``

-  ``[1,2,3]`` means ``1 :: 2 :: 3 :: Nil``

The library also defines a number of functions for manipulating these
types. ``map`` is overloaded both for ``List`` and ``Vect`` and
applies a function to every element of the list or vector.

.. code-block:: idris

    map : (a -> b) -> List a -> List b
    map f []        = []
    map f (x :: xs) = f x :: map f xs

    map : (a -> b) -> Vect n a -> Vect n b
    map f []        = []
    map f (x :: xs) = f x :: map f xs

For example, given the following vector of integers, and a function to
double an integer:

.. code-block:: idris

    intVec : Vect 5 Int
    intVec = [1, 2, 3, 4, 5]

    double : Int -> Int
    double x = x * 2

the function ``map`` can be used as follows to double every element in
the vector:

::

    *UsefulTypes> show (map double intVec)
    "[2, 4, 6, 8, 10]" : String

For more details of the functions available on ``List`` and
``Vect``, look in the library files:

-  ``libs/prelude/Prelude/List.idr``

-  ``libs/base/Data/List.idr``

-  ``libs/base/Data/Vect.idr``

-  ``libs/base/Data/VectType.idr``

Functions include filtering, appending, reversing, and so on.

Aside: Anonymous functions and operator sections
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

There are actually neater ways to write the above expression. One way
would be to use an anonymous function:

::

    *UsefulTypes> show (map (\x => x * 2) intVec)
    "[2, 4, 6, 8, 10]" : String

The notation ``\x => val`` constructs an anonymous function which takes
one argument, ``x`` and returns the expression ``val``. Anonymous
functions may take several arguments, separated by commas,
e.g. ``\x, y, z => val``. Arguments may also be given explicit types,
e.g. ``\x : Int => x * 2``, and can pattern match,
e.g. ``\(x, y) => x + y``. We could also use an operator section:

::

    *UsefulTypes> show (map (* 2) intVec)
    "[2, 4, 6, 8, 10]" : String

``(*2)`` is shorthand for a function which multiplies a number
by 2. It expands to ``\x => x * 2``. Similarly, ``(2*)`` would expand
to ``\x => 2 * x``.

Maybe
-----

``Maybe`` describes an optional value. Either there is a value of the
given type, or there isn’t:

.. code-block:: idris

    data Maybe a = Just a | Nothing

``Maybe`` is one way of giving a type to an operation that may
fail. For example, looking something up in a ``List`` (rather than a
vector) may result in an out of bounds error:

.. code-block:: idris

    list_lookup : Nat -> List a -> Maybe a
    list_lookup _     Nil         = Nothing
    list_lookup Z     (x :: xs) = Just x
    list_lookup (S k) (x :: xs) = list_lookup k xs

The ``maybe`` function is used to process values of type ``Maybe``,
either by applying a function to the value, if there is one, or by
providing a default value:

.. code-block:: idris

    maybe : Lazy b -> Lazy (a -> b) -> Maybe a -> b

Note that the types of the first two arguments are wrapped in
``Lazy``. Since only one of the two arguments will actually be used,
we mark them as ``Lazy`` in case they are large expressions where it
would be wasteful to compute and then discard them.

Tuples
------

Values can be paired with the following built-in data type:

.. code-block:: idris

    data Pair a b = MkPair a b

As syntactic sugar, we can write ``(a, b)`` which, according to
context, means either ``Pair a b`` or ``MkPair a b``. Tuples can
contain an arbitrary number of values, represented as nested pairs:

.. code-block:: idris

    fred : (String, Int)
    fred = ("Fred", 42)

    jim : (String, Int, String)
    jim = ("Jim", 25, "Cambridge")

::

    *UsefulTypes> fst jim
    "Jim" : String
    *UsefulTypes> snd jim
    (25, "Cambridge") : (Int, String)
    *UsefulTypes> jim == ("Jim", (25, "Cambridge"))
    True : Bool

Dependent Pairs
---------------

Dependent pairs allow the type of the second element of a pair to depend
on the value of the first element:

.. code-block:: idris

    data DPair : (a : Type) -> (P : a -> Type) -> Type where
       MkDPair : {P : a -> Type} -> (x : a) -> P x -> DPair a P

Again, there is syntactic sugar for this. ``(a : A ** P)`` is the type
of a pair of A and P, where the name ``a`` can occur inside ``P``.
``( a ** p )`` constructs a value of this type. For example, we can
pair a number with a ``Vect`` of a particular length:

.. code-block:: idris

    vec : (n : Nat ** Vect n Int)
    vec = (2 ** [3, 4])

If you like, you can write it out the long way, the two are precisely
equivalent:

.. code-block:: idris

    vec : DPair Nat (\n => Vect n Int)
    vec = MkDPair 2 [3, 4]

The type checker could of course infer the value of the first element
from the length of the vector. We can write an underscore ``_`` in
place of values which we expect the type checker to fill in, so the
above definition could also be written as:

.. code-block:: idris

    vec : (n : Nat ** Vect n Int)
    vec = (_ ** [3, 4])

We might also prefer to omit the type of the first element of the
pair, since, again, it can be inferred:

.. code-block:: idris

    vec : (n ** Vect n Int)
    vec = (_ ** [3, 4])

One use for dependent pairs is to return values of dependent types
where the index is not necessarily known in advance. For example, if
we filter elements out of a ``Vect`` according to some predicate, we
will not know in advance what the length of the resulting vector will
be:

.. code-block:: idris

    filter : (a -> Bool) -> Vect n a -> (p ** Vect p a)

If the ``Vect`` is empty, the result is easy:

.. code-block:: idris

    filter p Nil = (_ ** [])

In the ``::`` case, we need to inspect the result of a recursive call
to ``filter`` to extract the length and the vector from the result. To
do this, we use ``with`` notation, which allows pattern matching on
intermediate values:

.. code-block:: idris

    filter p (x :: xs) with (filter p xs)
      | ( _ ** xs' ) = if (p x) then ( _ ** x :: xs' ) else ( _ ** xs' )

We will see more on ``with`` notation later.

Dependent pairs are sometimes referred to as “Sigma types”.

Records
-------

*Records* are data types which collect several values (the record's
*fields*) together. Idris provides syntax for defining records and
automatically generating field access and update functions. Unlike
the syntax used for data structures, records in Idris follow a
different syntax to that seen with Haskell. For example, we can
represent a person’s name and age in a record:

.. code-block:: idris

    record Person where
        constructor MkPerson
        firstName, middleName, lastName : String
        age : Int

    fred : Person
    fred = MkPerson "Fred" "Joe" "Bloggs" 30

The constructor name is provided using the ``constructor`` keyword,
and the *fields* are then given which are in an indented block
following the `where` keyword (here, ``firstName``, ``middleName``,
``lastName``, and ``age``). You can declare multiple fields on a
single line, provided that they have the same type. The field names
can be used to access the field values:

::

    *Record> firstName fred
    "Fred" : String
    *Record> age fred
    30 : Int
    *Record> :t firstName
    firstName : Person -> String

We can also use the field names to update a record (or, more
precisely, produce a copy of the record with the given fields
updated):

.. code-block:: bash

    *Record> record { firstName = "Jim" } fred
    MkPerson "Jim" "Joe" "Bloggs" 30 : Person
    *Record> record { firstName = "Jim", age $= (+ 1) } fred
    MkPerson "Jim" "Joe" "Bloggs" 31 : Person

The syntax ``record { field = val, ... }`` generates a function which
updates the given fields in a record. ``=`` assigns a new value to a field,
and ``$=`` applies a function to update its value.

Each record is defined in its own namespace, which means that field names
can be reused in multiple records.

Records, and fields within records, can have dependent types. Updates
are allowed to change the type of a field, provided that the result is
well-typed.

.. code-block:: idris

    record Class where
        constructor ClassInfo
        students : Vect n Person
        className : String

It is safe to update the ``students`` field to a vector of a different
length because it will not affect the type of the record:

.. code-block:: idris

    addStudent : Person -> Class -> Class
    addStudent p c = record { students = p :: students c } c

::

    *Record> addStudent fred (ClassInfo [] "CS")
    ClassInfo [MkPerson "Fred" "Joe" "Bloggs" 30] "CS" : Class

We could also use ``$=`` to define ``addStudent`` more concisely:

.. code-block:: idris

    addStudent' : Person -> Class -> Class
    addStudent' p c = record { students $= (p ::) } c

Nested record update
~~~~~~~~~~~~~~~~~~~~

Idris also provides a convenient syntax for accessing and updating
nested records. For example, if a field is accessible with the
expression ``c (b (a x))``, it can be updated using the following
syntax:

.. code-block:: idris

    record { a->b->c = val } x

This returns a new record, with the field accessed by the path
``a->b->c`` set to ``val``. The syntax is first class, i.e. ``record {
a->b->c = val }`` itself has a function type. Symmetrically, the field
can also be accessed with the following syntax:

.. code-block:: idris

    record { a->b->c } x

The ``$=`` notation is also valid for nested record updates.

Dependent Records
-----------------

Records can also be dependent on values. Records have *parameters*, which
cannot be updated like the other fields. The parameters appear as arguments
to the resulting type, and are written following the record type
name. For example, a pair type could be defined as follows:

.. code-block:: idris

    record Prod a b where
        constructor Times
        fst : a
        snd : b

Using the ``class`` record from earlier, the size of the class can be
restricted using a ``Vect`` and the size included in the type by parameterising
the record with the size.  For example:

.. code-block:: idris

    record SizedClass (size : Nat) where
        constructor SizedClassInfo
        students : Vect size Person
        className : String

**Note** that it is no longer possible to use the ``addStudent``
function from earlier, since that would change the size of the class. A
function to add a student must now specify in the type that the
size of the class has been increased by one. As the size is specified
using natural numbers, the new value can be incremented using the
``S`` constructor:

.. code-block:: idris

    addStudent : Person -> SizedClass n -> SizedClass (S n)
    addStudent p c =  SizedClassInfo (p :: students c) (className c)

.. _sect-more-expr:

More Expressions
================

``let`` bindings
----------------

Intermediate values can be calculated using ``let`` bindings:

.. code-block:: idris

   mirror : List a -> List a
   mirror xs = let xs' = reverse xs in
                   xs ++ xs'

We can do simple pattern matching in ``let`` bindings too. For
example, we can extract fields from a record as follows, as well as by
pattern matching at the top level:

.. code-block:: idris

    data Person = MkPerson String Int

    showPerson : Person -> String
    showPerson p = let MkPerson name age = p in
                       name ++ " is " ++ show age ++ " years old"

List comprehensions
-------------------

Idris provides *comprehension* notation as a convenient shorthand
for building lists. The general form is:

::

    [ expression | qualifiers ]

This generates the list of values produced by evaluating the
``expression``, according to the conditions given by the comma
separated ``qualifiers``. For example, we can build a list of
Pythagorean triples as follows:

.. code-block:: idris

    pythag : Int -> List (Int, Int, Int)
    pythag n = [ (x, y, z) | z <- [1..n], y <- [1..z], x <- [1..y],
                             x*x + y*y == z*z ]

The ``[a..b]`` notation is another shorthand which builds a list of
numbers between ``a`` and ``b``. Alternatively ``[a,b..c]`` builds a
list of numbers between ``a`` and ``c`` with the increment specified
by the difference between ``a`` and ``b``. This works for type ``Nat``,
``Int`` and ``Integer``, using the ``enumFromTo`` and ``enumFromThenTo``
function from the prelude.

``case`` expressions
--------------------

Another way of inspecting intermediate values of *simple* types is to
use a ``case`` expression. The following function, for example, splits
a string into two at a given character:

.. code-block:: idris

    splitAt : Char -> String -> (String, String)
    splitAt c x = case break (== c) x of
                      (x, y) => (x, strTail y)

``break`` is a library function which breaks a string into a pair of
strings at the point where the given function returns true. We then
deconstruct the pair it returns, and remove the first character of the
second string.

A ``case`` expression can match several cases, for example, to inspect
an intermediate value of type ``Maybe a``. Recall ``list_lookup``
which looks up an index in a list, returning ``Nothing`` if the index
is out of bounds. We can use this to write ``lookup_default``, which
looks up an index and returns a default value if the index is out of
bounds:

.. code-block:: idris

    lookup_default : Nat -> List a -> a -> a
    lookup_default i xs def = case list_lookup i xs of
                                  Nothing => def
                                  Just x => x

If the index is in bounds, we get the value at that index, otherwise
we get a default value:

::

    *UsefulTypes> lookup_default 2 [3,4,5,6] (-1)
    5 : Integer
    *UsefulTypes> lookup_default 4 [3,4,5,6] (-1)
    -1 : Integer

**Restrictions:** The ``case`` construct is intended for simple
analysis of intermediate expressions to avoid the need to write
auxiliary functions, and is also used internally to implement pattern
matching ``let`` and lambda bindings. It will *only* work if:

- Each branch *matches* a value of the same type, and *returns* a
  value of the same type.

- The type of the result is “known”. i.e. the type of the expression
  can be determined *without* type checking the ``case``-expression
  itself.

Totality
========

Idris distinguishes between *total* and *partial* functions.
A total function is a function that either:

+ Terminates for all possible inputs, or
+ Produces a non-empty, finite, prefix of a possibly infinite result

If a function is total, we can consider its type a precise description of what
that function will do. For example, if we have a function with a return
type of ``String`` we know something different, depending on whether or not
it's total:

+ If it's total, it will return a value of type ``String`` in finite time;
+ If it's partial, then as long as it doesn't crash or enter an infinite loop,
  it will return a ``String``.

Idris makes this distinction so that it knows which functions are safe to
evaluate while type checking (as we've seen with :ref:`sect-fctypes`). After all,
if it tries to evaluate a function during type checking which doesn't
terminate, then type checking won't terminate!
Therefore, only total functions will be evaluated during type checking.
Partial functions can still be used in types, but will not be evaluated
further.
