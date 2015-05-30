**************
Miscellaneous
**************

Things we have yet to classify, or are two small to justify their own page.


Alternatives
============

The syntax ``(| x, y, z |)`` means to try elaborating all three options
and keep the one that works. This is used, for example, when translating
integer literals.

::

    Idris> the Nat (| "foo", Z, (-3) |)
    0 : Nat

"with"-expressions
==================

The syntax ``with NAME EXPR`` causes members of the namespace ``NAME``
to be privileged when resolving overloading. This is particularly useful
at the REPL:

::

    Idris> [1,2,3]
    Can't disambiguate name: Prelude.List.::, Prelude.Stream.::, Prelude.Vect.::
    Idris> with Vect [1,2,3]
    [1, 2, 3] : Vect 3 Integer

The Unifier Log
===============

If you're having a hard time debugging why the unifier won't accept
something (often while debugging the compiler itself), try applying the
special operator ``%unifyLog`` to the expression in question. This will
cause the type checker to spit out all sorts of informative messages.



Pattern matching on Implicit Arguments
======================================

Pattern matching is only allowed on implicit arguments when they are
referred by name, e.g.

.. code:: idris

    foo : {n : Nat} -> Nat
    foo {n = Z} = Z
    foo {n = S k} = k

or

.. code:: idris

    foo : {n : Nat} -> Nat
    foo {n = n} = n

The latter could be shortened to the following:

.. code:: idris

    foo : {n : Nat} -> Nat
    foo {n} = n

That is, ``{x}`` behaves like ``{x=x}``.


Existence of an instance
========================

In order to show that an instance of some typeclass is defined for some
type, one could use the ``%instance`` keyword:

.. code:: idris

    foo : Num Nat
    foo = %instance
