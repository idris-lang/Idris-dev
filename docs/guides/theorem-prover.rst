*******************************
The Interactive Theorem Prover
*******************************

This short guide contributed by a community member illustrates how to prove associativity of addition on ``Nat`` using the interactive theorem prover.

First we define a module ``Foo.idr``

.. code-block:: idris

    module Foo

    plusAssoc : plus n (plus m o) = plus (plus n m) o
    plusAssoc = ?rhs

We wish to perform induction on ``n``. First we load the file into the Idris ``REPL`` as follows::

    $ idris Foo.idr

We will be given the following prompt, in future releases the version string will differ::

         ____    __     _
        /  _/___/ /____(_)____
        / // __  / ___/ / ___/     Version 0.9.18.1
      _/ // /_/ / /  / (__  )      http://www.idris-lang.org/
     /___/\__,_/_/  /_/____/       Type :? for help

    Idris is free software with ABSOLUTELY NO WARRANTY.
    For details type :warranty.
    Type checking ./Foo.idr
    Metavariables: Foo.rhs
    *Foo>


Explore the Context
====================

We start the interactive session by asking Idris to prove the
hole ``rhs`` using the command ``:p rhs``. Idris by default
will show us the initial context. This looks as follows::

    *Foo> :p rhs
    ----------                 Goal:                  ----------
    { hole 0 }:
     (n : Nat) ->
     (m : Nat) ->
     (o : Nat) ->
     plus n (plus m o) = plus (plus n m) o

Application of Intros
=====================

We first apply the ``intros`` tactic::

    -Foo.rhs> intros
    ----------              Other goals:              ----------
    { hole 2 }
    { hole 1 }
    { hole 0 }
    ----------              Assumptions:              ----------
     n : Nat
     m : Nat
     o : Nat
    ----------                 Goal:                  ----------
    { hole 3 }:
     plus n (plus m o) = plus (plus n m) o

Induction on ``n``
==================

Then apply ``induction`` on to ``n``::

    -Foo.rhs> induction n
    ----------              Other goals:              ----------
    elim_S0
    { hole 2 }
    { hole 1 }
    { hole 0 }
    ----------              Assumptions:              ----------
     n : Nat
     m : Nat
     o : Nat
    ----------                 Goal:                  ----------
    elim_Z0:
     plus Z (plus m o) = plus (plus Z m) o


Compute
=======

::

    -Foo.rhs> compute
    ----------              Other goals:              ----------
    elim_S0
    { hole 2 }
    { hole 1 }
    { hole 0 }
    ----------              Assumptions:              ----------
     n : Nat
     m : Nat
     o : Nat
    ----------                 Goal:                  ----------
    elim_Z0:
     plus m o = plus m o

Trivial
=======

::

    -Foo.rhs> trivial
    ----------              Other goals:              ----------
    { hole 2 }
    { hole 1 }
    { hole 0 }
    ----------              Assumptions:              ----------
     n : Nat
     m : Nat
     o : Nat
    ----------                 Goal:                  ----------
    elim_S0:
     (n__0 : Nat) ->
     (plus n__0 (plus m o) = plus (plus n__0 m) o) ->
     plus (S n__0) (plus m o) = plus (plus (S n__0) m) o

Intros
======

::

    -Foo.rhs> intros
    ----------              Other goals:              ----------
    { hole 4 }
    elim_S0
    { hole 2 }
    { hole 1 }
    { hole 0 }
    ----------              Assumptions:              ----------
     n : Nat
     m : Nat
     o : Nat
     n__0 : Nat
     ihn__0 : plus n__0 (plus m o) = plus (plus n__0 m) o
    ----------                 Goal:                  ----------
    { hole 5 }:
     plus (S n__0) (plus m o) = plus (plus (S n__0) m) o


Compute
=======

::

    -Foo.rhs> compute
    ----------              Other goals:              ----------
    { hole 4 }
    elim_S0
    { hole 2 }
    { hole 1 }
    { hole 0 }
    ----------              Assumptions:              ----------
     n : Nat
     m : Nat
     o : Nat
     n__0 : Nat
     ihn__0 : plus n__0 (plus m o) = plus (plus n__0 m) o
    ----------                 Goal:                  ----------
    { hole 5 }:
     S (plus n__0 (plus m o)) = S (plus (plus n__0 m) o)


Rewrite
=======

::

    -Foo.rhs> rewrite ihn__0
    ----------              Other goals:              ----------
    { hole 5 }
    { hole 4 }
    elim_S0
    { hole 2 }
    { hole 1 }
    { hole 0 }
    ----------              Assumptions:              ----------
     n : Nat
     m : Nat
     o : Nat
     n__0 : Nat
     ihn__0 : plus n__0 (plus m o) = plus (plus n__0 m) o
    ----------                 Goal:                  ----------
    { hole 6 }:
     S (plus n__0 (plus m o)) = S (plus n__0 (plus m o))

Trivial
=======

::

    -Foo.rhs> trivial
    rhs: No more goals.
    -Foo.rhs> qed
    Proof completed!
    Foo.rhs = proof
      intros
      induction n
      compute
      trivial
      intros
      compute
      rewrite ihn__0
      trivial

Two goals were created: one for ``Z`` and one for ``S``.
Here we have proven associativity, and assembled a tactic based proof script.
This proof script can be added to ``Foo.idr``.
