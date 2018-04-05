**************************
Frequently Asked Questions
**************************

What are the differences between Agda and Idris?
================================================

Like Idris, Agda is a functional language with dependent types, supporting
dependent pattern matching. Both can be used for writing programs and proofs.
However, Idris has been designed from the start to emphasise general purpose
programming rather than theorem proving. As such, it supports interoperability
with systems libraries and C programs, and language constructs for
domain specific language implementation. It also includes higher level
programming constructs such as interfaces (similar to type classes) and do notation.

Idris supports multiple back ends (C and JavaScript by default, with the
ability to add more via plugins) and has a reference run time system, written
in C, with a garbage collector and built-in message passing concurrency.


Is Idris production ready?
==========================

Idris is primarily a research tool for exploring the possibilities of software
development with dependent types, meaning that the primary goal is not (yet) to
make a system which could be used in production. As such, there are a few rough
corners, and lots of missing libraries. Nobody is working on Idris full time,
and we don't have the resources at the moment to polish the system on our own.
Therefore, we don't recommend building your business around it!

Having said that, contributions which help towards making Idris suitable
for use in production would be very welcome - this includes (but is not
limited to) extra library support, polishing the run-time system (and ensuring
it is robust), providing and maintaining a JVM back end, etc.


Why does Idris use eager evaluation rather than lazy?
=====================================================

Idris uses eager evaluation for more predictable performance, in particular
because one of the longer term goals is to be able to write efficient and
verified low level code such as device drivers and network infrastructure.
Furthermore, the Idris type system allows us to state precisely the type
of each value, and therefore the run-time form of each value. In a lazy
language, consider a value of type ``Int``:

.. code-block:: idris

    thing : Int

What is the representation of ``thing`` at run-time? Is it a bit pattern
representing an integer, or is it a pointer to some code which will compute
an integer? In Idris, we have decided that we would like to make this
distinction precise, in the type:

.. code-block:: idris

    thing_val : Int
    thing_comp : Lazy Int

Here, it is clear from the type that ``thing_val`` is guaranteed to be a
concrete ``Int``, whereas ``thing_comp`` is a computation which will produce an
``Int``.


How can I make lazy control structures?
=======================================

You can make control structures using the special Lazy type. For
example, ``if...then...else...`` in Idris expands to an application of
a function named ``ifThenElse``. The default implementation for
Booleans is defined as follows in the library:

.. code-block:: idris

    ifThenElse : Bool -> (t : Lazy a) -> (e : Lazy a) -> a
    ifThenElse True  t e = t
    ifThenElse False t e = e

The type ``Lazy a`` for ``t`` and ``e`` indicates that those arguments will
only be evaluated if they are used, that is, they are evaluated lazily.


Evaluation at the REPL doesn't behave as I expect. What's going on?
===================================================================

Being a fully dependently typed language, Idris has two phases where it
evaluates things, compile-time and run-time. At compile-time it will only
evaluate things which it knows to be total (i.e. terminating and covering all
possible inputs) in order to keep type checking decidable. The compile-time
evaluator is part of the Idris kernel, and is implemented in Haskell using a
HOAS (higher order abstract syntax) style representation of values. Since
everything is known to have a normal form here, the evaluation strategy doesn't
actually matter because either way it will get the same answer, and in practice
it will do whatever the Haskell run-time system chooses to do.

The REPL, for convenience, uses the compile-time notion of evaluation. As well
as being easier to implement (because we have the evaluator available) this can
be very useful to show how terms evaluate in the type checker. So you can see
the difference between:

.. code-block:: idris

    Idris> \n, m => (S n) + m
    \n => \m => S (plus n m) : Nat -> Nat -> Nat

    Idris> \n, m => n + (S m)
    \n => \m => plus n (S m) : Nat -> Nat -> Nat


Why can't I use a function with no arguments in a type?
=======================================================

If you use a name in a type which begins with a lower case letter, and which is
not applied to any arguments, then Idris will treat it as an implicitly
bound argument. For example:

.. code-block:: idris

    append : Vect n ty -> Vect m ty -> Vect (n + m) ty

Here, ``n``, ``m``, and ``ty`` are implicitly bound. This rule applies even
if there are functions defined elsewhere with any of these names. For example,
you may also have:

.. code-block:: idris

    ty : Type
    ty = String

Even in this case, ``ty`` is still considered implicitly bound in the definition
of ``append``, rather than making the type of ``append`` equivalent to...

.. code-block:: idris

    append : Vect n String -> Vect m String -> Vect (n + m) String

...which is probably not what was intended!  The reason for this rule is so
that it is clear just from looking at the type of ``append``, and no other
context, what the implicitly bound names are.

If you want to use an unapplied name in a type, you have two options. You
can either explicitly qualify it, for example, if ``ty`` is defined in the
namespace ``Main`` you can do the following:

.. code-block:: idris

    append : Vect n Main.ty -> Vect m Main.ty -> Vect (n + m) Main.ty

Alternatively, you can use a name which does not begin with a lower case
letter, which will never be implicitly bound:

.. code-block:: idris

    Ty : Type
    Ty = String

    append : Vect n Ty -> Vect m Ty -> Vect (n + m) Ty

As a convention, if a name is intended to be used as a type synonym, it is
best for it to begin with a capital letter to avoid this restriction.


I have an obviously terminating program, but Idris says it possibly isn't total. Why is that?
=============================================================================================

Idris can't decide in general whether a program is terminating due to
the undecidability of the `Halting Problem
<https://en.wikipedia.org/wiki/Halting_problem>`_. It is possible, however,
to identify some programs which are definitely terminating. Idris does this
using "size change termination" which looks for recursive paths from a
function back to itself. On such a path, there must be at least one
argument which converges to a base case.

- Mutually recursive functions are supported

- However, all functions on the path must be fully applied. In particular,
  higher order applications are not supported

- Idris identifies arguments which converge to a base case by looking for
  recursive calls to syntactically smaller arguments of inputs. e.g.
  ``k`` is syntactically smaller than ``S (S k)`` because ``k`` is a
  subterm of ``S (S k)``, but ``(k, k)`` is
  not syntactically smaller than ``(S k, S k)``.

If you have a function which you believe to be terminating, but Idris does
not, you can either restructure the program, or use the ``assert_total``
function.


When will Idris be self-hosting?
================================

It’s not a priority, though not a bad idea in the long run. It would be a
worthwhile effort in the short term to implement libraries to support
self-hosting, such as a good parsing library.


Does Idris have universe polymorphism? What is the type of ``Type``?
====================================================================

Rather than universe polymorphism, Idris has a cumulative hierarchy of
universes; ``Type : Type 1``, ``Type 1 : Type 2``, etc.
Cumulativity means that if ``x : Type n`` and ``n <= m``, then
``x : Type m``. Universe levels are always inferred by Idris, and
cannot be specified explicitly. The REPL command ``:type Type 1`` will
result in an error, as will attempting to specify the universe level
of any type.


Why does Idris use ``Double`` instead of ``Float64``?
=====================================================

Historically the C language and many other languages have used the
names ``Float`` and ``Double`` to represent floating point numbers of
size 32 and 64 respectively.  Newer languages such as Rust and Julia
have begun to follow the naming scheme described in `IEEE Standard for
Floating-Point Arithmetic (IEEE 754)
<https://en.wikipedia.org/wiki/IEEE_floating_point>`_. This describes
single and double precision numbers as ``Float32`` and ``Float64``;
the size is described in the type name.

Due to developer familiarity with the older naming convention, and
choice by the developers of Idris, Idris uses the C style convention.
That is, the name ``Double`` is used to describe double precision
numbers, and Idris does not support 32 bit floats at present.


What is -ffreestanding?
=======================

The freestanding flag is used to build Idris binaries which have their
libs and compiler in a relative path. This is useful for building binaries
where the install directory is unknown at build time. When passing this
flag, the IDRIS_LIB_DIR environment variable needs to be set to the path
where the Idris libs reside relative to the idris executable. The
IDRIS_TOOLCHAIN_DIR environment variable is optional, if that is set,
Idris will use that path to find the C compiler. For example:

::

   IDRIS_LIB_DIR="./libs" \
   IDRIS_TOOLCHAIN_DIR="./mingw/bin" \
   CABALFLAGS="-fffi -ffreestanding -frelease" \
   make


What does the name “Idris” mean?
================================

British people of a certain age may be familiar with this
`singing dragon <https://www.youtube.com/watch?v=G5ZMNyscPcg>`_. If
that doesn’t help, maybe you can invent a suitable acronym :-) .


Will there be support for Unicode characters for operators?
===========================================================

There are several reasons why we should not support Unicode operators:

- It's hard to type (this is important if you're using someone else's code, for
  example). Various editors have their own input methods, but you have to know
  what they are.

- Not every piece of software easily supports it. Rendering issues have been
  noted on some mobile email clients, terminal-based IRC clients, web browsers,
  etc. There are ways to resolve these rendering issues but they provide a
  barrier to entry to using Idris.

- Even if we leave it out of the standard library (which we will in any case!)
  as soon as people start using it in their library code, others have to deal
  with it.

- Too many characters look too similar. We had enough trouble with confusion
  between 0 and O without worrying about all the different kinds of colons and
  brackets.

- There seems to be a tendency to go over the top with use of Unicode. For
  example, using sharp and flat for delay and force (or is it the other way
  around?) in Agda seems gratuitous. We don't want to encourage this sort of
  thing, when words are often better.

With care, Unicode operators can make things look pretty but so can ``lhs2TeX``.
Perhaps in a few years time things will be different and software will cope
better and it will make sense to revisit this. For now, however, Idris will not
be offering arbitrary Unicode symbols in operators.

This seems like an instance of `Wadler's
Law <http://www.haskell.org/haskellwiki/Wadler%27s_Law>`__ in action.

This answer is based on Edwin Brady's response in the following
`pull request <https://github.com/idris-lang/Idris-dev/pull/694#issuecomment-29559291>`_.

Where can I find the community standards for the Idris community?
==================================================================

The Idris Community Standards are stated `here
<https://www.idris-lang.org/documentation/community-standards/>`_ .

Where can I find more answers?
==============================

There is an `Unofficial FAQ
<https://github.com/idris-lang/Idris-dev/wiki/Unofficial-FAQ>`_ on the wiki on
GitHub which answers more technical questions and may be updated more often.
