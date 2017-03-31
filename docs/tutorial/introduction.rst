.. _sect-intro:

************
Introduction
************

In conventional programming languages, there is a clear distinction
between *types* and *values*. For example, in `Haskell
<http://www.haskell.org>`_, the following are types, representing
integers, characters, lists of characters, and lists of any value
respectively:

-  ``Int``, ``Char``, ``[Char]``, ``[a]``

Correspondingly, the following values are examples of inhabitants of
those types:

-  ``42``, ``’a’``, ``"Hello world!"``, ``[2,3,4,5,6]``

In a language with *dependent types*, however, the distinction is less
clear. Dependent types allow types to “depend” on values — in other
words, types are a *first class* language construct and can be
manipulated like any other value. The standard example is the type of
lists of a given length [1]_, ``Vect n a``, where ``a`` is the element
type and ``n`` is the length of the list and can be an arbitrary term.

When types can contain values, and where those values describe
properties, for example the length of a list, the type of a function
can begin to describe its own properties. Take for example the
concatenation of two lists. This operation has the property that the
resulting list's length is the sum of the lengths of the two input
lists. We can therefore give the following type to the ``app``
function, which concatenates vectors:

.. code-block:: idris

    app : Vect n a -> Vect m a -> Vect (n + m) a

This tutorial introduces Idris, a general purpose functional
programming language with dependent types. The goal of the Idris
project is to build a dependently typed language suitable for
verifiable general purpose programming. To this end, Idris is a compiled
language which aims to generate efficient executable code. It also has
a lightweight foreign function interface which allows easy interaction
with external ``C`` libraries.

Intended Audience
=================

This tutorial is intended as a brief introduction to the language, and
is aimed at readers already familiar with a functional language such
as `Haskell <http://www.haskell.org>`_ or `OCaml <http://ocaml.org>`_.
In particular, a certain amount of familiarity with Haskell syntax is
assumed, although most concepts will at least be explained
briefly. The reader is also assumed to have some interest in using
dependent types for writing and verifying systems software.

For a more in-depth introduction to Idris, which proceeds at a much slower
pace, covering interactive program development, with many more examples, see
`Type-Driven Development with Idris <https://www.manning.com/books/type-driven-development-with-idris>`_
by Edwin Brady, available from `Manning <https://www.manning.com>`_.

Example Code
============

This tutorial includes some example code, which has been tested with
against Idris. These files are available with the Idris distribution,
so that you can try them out easily. They can be found under
``samples``. It is, however, strongly recommended that you type
them in yourself, rather than simply loading and reading them.

.. [1]
   Typically, and perhaps confusingly, referred to in the dependently
   typed programming literature as “vectors”
