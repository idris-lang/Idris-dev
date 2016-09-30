****************
Uniqueness Types
****************

Uniqueness Types are an experimental feature available from Idris
0.9.15. A value with a unique type is guaranteed to have *at most one*
reference to it at run-time, which means that it can safely be updated
in-place, reducing the need for memory allocation and garbage
collection. The motivation is that we would like to be able to write
reactive systems, programs which run in limited memory environments,
device drivers, and any other system with hard real-time requirements,
ideally while giving up as little high level conveniences as possible.

They are inspired by linear types, `Uniqueness Types
<https://en.wikipedia.org/wiki/Uniqueness_type>`__ in the `Clean
<http://wiki.clean.cs.ru.nl/Clean>`__ programming language, and
ownership types and borrowed pointers in the `Rust
<https://www.rust-lang.org/>`__ programming language.

Some things we hope to be able to do eventually with uniqueness types
include:

-  Safe, pure, in-place update of arrays, lists, etc
-  Provide guarantees of correct resource usage, state transitions, etc
-  Provide guarantees that critical program fragments will *never*
   allocate

Using Uniqueness
================

If ``x : T`` and ``T : UniqueType``, then there is at most one reference
to ``x`` at any time during run-time execution. For example, we can
declare the type of unique lists as follows:

.. code-block:: idris

    data UList : Type -> UniqueType where
         Nil   : UList a
         (::)  : a -> UList a -> UList a

If we have a value ``xs : UList a``, then there is at most one
reference to ``xs`` at run-time. The type checker preserves this
guarantee by ensuring that there is at most one reference to any value
of a unique type in a pattern clause. For example, the following
function definition would be valid:

.. code-block:: idris

    umap : (a -> b) -> UList a -> UList b
    umap f [] = []
    umap f (x :: xs) = f x :: umap f xs

In the second clause, ``xs`` is a value of a unique type, and only
appears once on the right hand side, so this clause is valid. Not only
that, since we know there can be no other reference to the ``UList a``
argument, we can reuse its space for building the result! The compiler
is aware of this, and compiles this definition to an in-place update
of the list.

The following function definition would not be valid (even assuming an
implementation of ``++``), however, since ``xs`` appears twice:

.. code-block:: idris

    dupList : UList a -> UList a
    dupList xs = xs ++ xs

This would result in a shared pointer to ``xs``, so the typechecker
reports:

.. code-block:: idris

    unique.idr:12:5:Unique name xs is used more than once

If we explicitly copy, however, the typechecker is happy:

.. code-block:: idris

    dup : UList a -> UList a
    dup [] = []
    dup (x :: xs) = x :: x :: dup xs

Note that it's fine to use ``x`` twice, because ``a`` is a ``Type``,
rather than a ``UniqueType``.

There are some other restrictions on where a ``UniqueType`` can
appear, so that the uniqueness property is preserved. In particular,
the type of the function type, ``(x : a) -> b`` depends on the type of
``a`` or ``b`` - if either is a ``UniqueType``, then the function type
is also a ``UniqueType``. Then, in a data declaration, if the type
constructor builds a ``Type``, then no constructor can have a
``UniqueType``. For example, the following definition is invalid,
since it would embed a unique value in a possible non-unique value:

.. code-block:: idris

    data BadList : UniqueType -> Type where
         Nil   : {a : UniqueType} -> BadList a
         (::)  : {a : UniqueType} -> a -> BadList a -> BadList a

Finally, types may be polymorphic in their uniqueness, to a limited
extent. Since ``Type`` and ``UniqueType`` are different types, we are
limited in how much we can use polymorphic functions on unique types.
For example, if we have function composition defined as follows:

.. code-block:: idris

    (.) : {a, b, c : Type} -> (b -> c) -> (a -> b) -> a -> c
    (.) f g x = f (g x)

And we have some functions over unique types:

.. code-block:: idris

    foo : UList a -> UList b
    bar : UList b -> UList c

Then we cannot compose ``foo`` and ``bar`` as ``bar . foo``, because
``UList`` does not compute a ``Type``! Instead, we can define
composition as follows:

.. code-block:: idris

    (.) : {a, b, c : Type*} -> (b -> c) -> (a -> b) -> a -> c
    (.) f g x = f (g x)

The ``Type*`` type stands for either unique or non-unique types. Since
such a function may be passed a ``UniqueType``, any value of type
``Type*`` must also satisfy the requirement that it appears at most
once on the right hand side.

Borrowed Types
--------------

It quickly becomes obvious when working with uniqueness types that
having only one reference at a time can be painful. For example, what
if we want to display a list before updating it?

.. code-block:: idris

    showU : Show a => UList a -> String
    showU xs = "[" ++ showU' xs ++ "]" where
      showU' : UList a -> String
      showU' [] = ""
      showU' [x] = show x
      showU' (x :: xs) = show x ++ ", " ++ showU' xs

This is a valid definition of ``showU``, but unfortunately it consumes
the list! So the following function would be invalid:

.. code-block:: idris

    printAndUpdate : UList Int -> IO ()
    printAndUpdate xs = do putStrLn (showU xs)
                           let xs' = umap (*2) xs -- xs no longer available!
                           putStrLn (showU xs')

Still, one would hope to be able to display a unique list without
problem, since it merely *inspects* the list; there are no updates. We
can achieve this, using the notion of *borrowing*. A Borrowed type is
a Unique type which can be inspected at the top level (by pattern
matching, or by *lending* to another function) but no further. This
ensures that the internals (i.e. the arguments to top level patterns)
will not be passed to any function which will update them.

``Borrowed`` converts a ``UniqueType`` to a ``BorrowedType``. It is
defined as follows (along with some additional rules in the
typechecker):

.. code-block:: idris

    data Borrowed : UniqueType -> BorrowedType where
         Read : {a : UniqueType} -> a -> Borrowed a

    implicit
    lend : {a : UniqueType} -> a -> Borrowed a
    lend x = Read x

A value can be "lent" to another function using ``lend``. Arguments to
``lend`` are not counted by the type checker as a reference to a unique
value, therefore a value can be lent as many times as desired. Using
this, we can write ``showU`` as follows:

.. code-block:: idris

    showU : Show a => Borrowed (UList a) -> String
    showU xs = "[" ++ showU' xs ++ "]" where
      showU' : Borrowed (UList a) -> String
      showU' [] = ""
      showU' [x] = show x
      showU' (Read (x :: xs)) = show x ++ ", " ++ showU' (lend xs)

Unlike a unique value, a borrowed value may be referred to as many
times as desired. However, there is a restriction on how a borrowed
value can be used. After all, much like a library book or your
neighbour's lawnmower, if a function borrows a value it is expected to
return it in exactly the condition in which it was received!

The restriction is that when a ``Borrowed`` type is matched, any
pattern variables under the ``Read`` which have a unique type may not
be referred to at all on the right hand side (unless they are
themselves ``lent`` to another function).

Uniqueness information is stored in the type, and in particular in
function types. Once we're in a unique context, any new function which
is constructed will be required to have unique type, which prevents
the following sort of bad program being implemented:

.. code-block:: idris

    foo : UList Int -> IO ()
    foo xs = do let f = \x : Int => showU xs
                putStrLn $ free xs
                putStrLn $ f 42
                pure ()

Since ``lend`` is implicit, in practice for functions to lend and borrow
values merely requires the argument to be marked as ``Borrowed``. We can
therefore write ``showU`` as follows:

.. code-block:: idris

    showU : Show a => Borrowed (UList a) -> String
    showU xs = "[" ++ showU' xs ++ "]" where
      showU' : Borrowed (UList a) -> String
      showU' [] = ""
      showU' [x] = show x
      showU' (x :: xs) = show x ++ ", " ++ showU' xs

Problems/Disadvantages/Still to do...
-------------------------------------

This is a work in progress, there is lots to do. The most obvious
problem is the loss of abstraction. On the one hand, we have more
precise control over memory usage with ``UniqueType`` and
``BorrowedType``, but they are not in general compatible with
functions polymorphic over ``Type``. In the short term, we can start
to write reactive and low memory systems with this, but longer term it
would be nice to support more abstraction.

We also haven't checked any of the metatheory, so this could all be
fatally flawed! The implementation is based to a large extent on
`Uniqueness Typing Simplified
<http://lambda-the-ultimate.org/node/2708>`__, by de Vries et al, so
there is reason to believe things should be fine, but we still have to
do the work.

Much as there are with linear types, there are some annoyances when
trying to prove properties of functions with unique types (for
example, what counts as a use of a value). Since we require *at most*
one use of a value, rather than *exactly* one, this seems to be less
of an issue in practice, but still needs thought.
