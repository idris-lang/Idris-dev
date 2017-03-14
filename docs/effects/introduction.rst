************
Introduction
************

Pure functional languages with dependent types such as `Idris
<http://www.idris-lang.org/>`_ support reasoning about programs directly
in the type system, promising that we can *know* a program will run
correctly (i.e. according to the specification in its type) simply
because it compiles. Realistically, though, things are not so simple:
programs have to interact with the outside world, with user input,
input from a network, mutable state, and so on. In this tutorial I
will introduce the library, which is included with the distribution
and supports programming and reasoning with side-effecting programs,
supporting mutable state, interaction with the outside world,
exceptions, and verified resource management.

This tutorial assumes familiarity with pure programming in Idris,
as described in Sections 1–6 of the main tutorial [1]_. The examples
presented are tested with Idris and can be found in the
examples directory of the Idris repository.

Consider, for example, the following introductory function which
illustrates the kind of properties which can be expressed in the type
system:

.. code-block:: idris

   vadd : Vect n Int -> Vect n Int -> Vect n Int
   vadd []        []        = []
   vadd (x :: xs) (y :: ys) = x + y :: vadd xs ys

This function adds corresponding elements in a pair of vectors. The type
guarantees that the vectors will contain only elements of type ``Int``,
and that the input lengths and the output length all correspond. A
natural question to ask here, which is typically neglected by
introductory tutorials, is “How do I turn this into a program?” That is,
given some lists entered by a user, how do we get into a position to be
able to apply the ``vadd`` function? Before doing so, we will have to:

- Read user input, either from the keyboard, a file, or some other input device.

- Check that the user inputs are valid, i.e. contain only ``Int`` and are the same length, and report an error if not.

- Write output

The complete program will include side-effects for I/O and error
handling, before we can get to the pure core functionality. In this
tutorial, we will see how Idris supports side-effects.
Furthermore, we will see how we can use the dependent type system to
*reason* about stateful and side-effecting programs. We will return to
this specific example later.

Hello world
===========

To give an idea of how programs with effects look, here is the
ubiquitous “Hello world” program, written using the ``Effects``
library:

.. code-block:: idris

   module Main

   import Effects
   import Effect.StdIO

   hello : Eff () [STDIO]
   hello = putStrLn “Hello world!”

   main : IO ()
   main = run hello

As usual, the entry point is ``main``. All ``main`` has to do is invoke the
``hello`` function which supports the ``STDIO`` effect for console I/O, and
returns the unit value.  All programs using the ``Effects`` library must
``import Effects``.  The details of the ``Eff`` type will be presented in the
remainder of this tutorial.

To compile and run this program, Idris needs to be told to include
the ``Effects`` package, using the ``-p effects`` flag (this flag is
required for all examples in this tutorial):

.. code-block:: sh

   idris hello.idr -o hello -p effects
   ./hello Hello world!

Outline
=======

The tutorial is structured as follows: first, in Section
:ref:`sect-state`, we will discuss state management, describing why it
is important and introducing the ``effects`` library to show how it
can be used to manage state. This section also gives an overview of
the syntax of effectful programs. Section :ref:`sect-simpleff` then
introduces a number of other effects a program may have: I/O;
Exceptions; Random Numbers; and Non-determinism, giving examples for
each, and an extended example combining several effects in one
complete program. Section :ref:`sect-depeff` introduces *dependent*
effects, showing how states and resources can be managed in
types. Section :ref:`sect-impleff` shows how new effects can be
implemented.  Section :ref:`sect-hangman` gives an extended example
showing how to implement a “mystery word” guessing game, using effects
to describe the rules of the game and ensure they are implemented
accurately. References to further reading are given in Section
:ref:`sect-further`.

.. [1]
   You do not, however, need to know what a monad is!
