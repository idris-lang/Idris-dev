****************************************
DEPRECATED: Tactics and Theorem Proving
****************************************

.. warning::
   The interactive theorem-proving interface documented here has been
   deprecated in favor of :ref:`elaborator-reflection`.

Idris supports interactive theorem proving, and the analyse of context
through holes.  To list all unproven holes, use the command ``:m``.
This will display their qualified names and the expected types. To
interactively prove a holes, use the command ``:p name`` where ``name``
is the hole. Once the proof is complete, the command ``:a`` will append
it to the current module.

Once in the interactive prover, the following commands are available:

Basic commands
==============

-  ``:q`` - Quits the prover (gives up on proving current lemma).
-  ``:abandon`` - Same as :q
-  ``:state`` - Displays the current state of the proof.
-  ``:term`` - Displays the current proof term complete with its
   yet-to-be-filled holes (is only really useful for debugging).
-  ``:undo`` - Undoes the last tactic.
-  ``:qed`` - Once the interactive theorem prover tells you "No more
   goals," you get to type this in celebration! (Completes the proof and
   exits the prover)

Commonly Used Tactics
=====================

Compute
-------

-  ``compute`` - Normalises all terms in the goal (note: does not
   normalise assumptions)

::

    ----------                 Goal:                  ----------
     (Vect (S (S Z + (S Z) + (S n))) Nat) -> Vect (S (S (S (S n)))) Nat
    -lemma> compute
    ----------                 Goal:                  ----------
     (Vect (S (S (S (S n)))) Nat) -> Vect (S (S (S (S n)))) Nat
    -lemma>

Exact
-----

-  ``exact`` - Provide a term of the goal type directly.

::

    ----------                 Goal:                  ----------
     Nat
    -lemma> exact Z
    lemma: No more goals.
    -lemma>

Refine
------

-  ``refine`` - Use a name to refine the goal. If the name needs
   arguments, introduce them as new goals.

Trivial
-------

-  ``trivial`` - Satisfies the goal using an assumption that matches its
   type.

::

    ----------              Assumptions:              ----------
     value : Nat
    ----------                 Goal:                  ----------
     Nat
    -lemma> trivial
    lemma: No more goals.
    -lemma>

Intro
-----

-  ``intro`` - If your goal is an arrow, turns the left term into an
   assumption.

::

    ----------                 Goal:                  ----------
     Nat -> Nat -> Nat
    -lemma> intro
    ----------              Assumptions:              ----------
     n : Nat
    ----------                 Goal:                  ----------
     Nat -> Nat
    -lemma>

You can also supply your own name for the assumption:

::

    ----------                 Goal:                  ----------
    Nat -> Nat -> Nat
    -lemma> intro number
    ----------              Assumptions:              ----------
     number : Nat
    ----------                 Goal:                  ----------
    Nat -> Nat


Intros
------

-  ``intros`` - Exactly like intro, but it operates on all left terms at
   once.

::

    ----------                 Goal:                  ----------
     Nat -> Nat -> Nat
    -lemma> intros
    ----------              Assumptions:              ----------
     n : Nat
     m : Nat
    ----------                 Goal:                  ----------
     Nat
    -lemma>

let
---

-  ``let`` - Introduces a new assumption; you may use current
   assumptions to define the new one.

::

    ----------              Assumptions:              ----------
     n : Nat
    ----------                 Goal:                  ----------
     BigInt
    -lemma> let x = toIntegerNat n
    ----------              Assumptions:              ----------
     n : Nat
      x = toIntegerNat n: BigInt
    ----------                 Goal:                  ----------
     BigInt
    -lemma>

rewrite
-------

-  ``rewrite`` - Takes an expression with an equality type (x = y), and
   replaces all instances of x in the goal with y. Is often useful in
   combination with 'sym'.

::

    ----------              Assumptions:              ----------
     n : Nat
     a : Type
     value : Vect Z a
    ----------                 Goal:                  ----------
     Vect (mult n Z) a
    -lemma> rewrite sym (multZeroRightZero n)
    ----------              Assumptions:              ----------
     n : Nat
     a : Type
     value : Vect Z a
    ----------                 Goal:                  ----------
     Vect Z a
    -lemma>

induction
---------

-  ``induction`` - (``Note that this is still experimental`` and you may
   get strange results and error messages. We are aware of these and
   will finish the implementation eventually!) Prove the goal by
   induction. Each constructor of the datatype becomes a goal.
   Constructors with recursive arguments become induction steps, while
   simple constructors become base cases. Note that this only works for
   datatypes that have eliminators: a datatype definition must have the
   ``%elim`` modifier.


sourceLocation
--------------

-  ``sourceLocation`` - Solve the current goal with information about
   the location in the source code where the tactic was invoked. This is
   mostly for embedded DSLs and programmer tools like assertions that
   need to know where they are called. See
   ``Language.Reflection.SourceLocation`` for more information.

Less commonly-used tactics
==========================

-  ``applyTactic`` - Apply a user-defined tactic. This should be a
   function of type ``List (TTName, Binder TT) -> TT -> Tactic``, where
   the first argument represents the proof context and the second
   represents the goal. If your tactic will produce a proof term
   directly, use the ``Exact`` constructor from ``Tactic``.
-  ``attack`` - ?
-  ``equiv`` - Replaces the goal with a new one that is convertible with
   the old one
-  ``fill`` - ?
-  ``focus`` - ?
-  ``mrefine`` - Refining by matching against a type
-  ``reflect`` - ?
-  ``solve`` - Takes a guess with the correct type and fills a hole with
   it, closing a proof obligation. This happens automatically in the
   interactive prover, so ``solve`` is really only relevant in tactic
   scripts used for helping implicit argument resolution.
-  ``try`` - ?
