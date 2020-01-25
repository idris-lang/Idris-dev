Elaborator Reflection - Holes
=============================

The process of doing proofs and elaborator reflection tends to involve stating with a desired conclusion and working back to known premises. This often needs intermediate sub-goals which may only be partially solved, these are encoded using 'holes' and 'guesses'.

* A hole is a term (an expression - a chunk of code) which is yet to be determined. We do have information about its type (this process tends to be type driven).
* A guess is like a hole that is not yet bound.

The theory around this was developed in `Dependently Typed Functional Programs and their Proofs by McBride 1999`_.

Notation for Holes and Guesses
------------------------------

There is a notation used in the McBride 1999 thesis which is adapted for the TT language. When working on elaborator reflection it is useful to know this notation, for instance when reading the output of the 'debug' tactic.

* A focused hole is notated like this ?x:t . t
* A guess is notated like this ?x ≈ t:t . t

The following example shows how this is used:

Simple Example
--------------

Start with a code file that just contains:

.. code-block:: idris

  %language ElabReflection

  testFn : Nat
  testFn = %runElab (do debug {a = ()})

when this is loaded the following is displayed:

.. code-block:: idris

  Holes:
        ----------------------------------
        {hole_2} : Prelude.Nat.Nat

        ----------------------------------
        {hole_0} : Prelude.Nat.Nat

  Term:
        ?{hole_0} ≈ ? {hole_2} . {hole_2} . {hole_0}

This shows information about the state when debug is encountered, during tactic execution, which allows us to investigate what is happening at each stage.

* The "Holes" part shows the types of the holes and the local context of each
* The "Term" part shows where these holes are in the expression being constructed.

So starting with the "Term" part we have.

.. code-block:: idris

  ?{hole_0} ≈ ? {hole_2} . {hole_2} . {hole_0}

.. sidebar:: attack tactic

  This kind of thing tends to arise from "attack", which helps keep binding forms in order.

The meaning of this is not immediately apparent so it helps to add some parentheses to make the structure clearer:

.. code-block:: idris

  (?{hole_0} ≈ (? {hole_2} . {hole_2}) . {hole_0})

First lets look at the inner part:

.. code-block:: idris

  ? {hole_2} . {hole_2}

We can substitute in the type from the "Holes" part:

.. code-block:: idris

  ? {hole_2}:Nat . {hole_2}:Nat

So we are looking for a hole of type Nat and all we know is it has type Nat.

Going back to the full term, the above is wrapped in a guess, so it means: 'a guess that is itself a hole'.

Since the elaborator does not have any further information it has to be given a value:

.. code-block:: idris

  %language ElabReflection

  testFn : Nat
  testFn = %runElab (do fill `(Z)
                        debug {a = ()}
                        solve)

Now we have a guess for hole_2 which is itself a guess for hole_0:

.. code-block:: idris

  ?{hole_0} ≈ ?{hole_2} ≈ Prelude.Nat.Z . {hole_2} . {hole_0}

The guesses can be accepted by calling the 'solve' tactic.

Example Showing Patterns
------------------------

In this next example a parameter 'n' has been added to the function. This allows us to see how patterns are used. Starting with this file:

.. code-block:: idris

  %language ElabReflection

  testFn : Nat -> Nat
  testFn n = %runElab (do debug {a = ()})

when loaded gives:

.. code-block:: idris

  Holes:
        n : Prelude.Nat.Nat
        ----------------------------------
        {hole_3} : Prelude.Nat.Nat

        n : Prelude.Nat.Nat
        ----------------------------------
        {hole_1} : Prelude.Nat.Nat

        ----------------------------------
        {hole_0} : patTy n : Prelude.Nat.Nat . Prelude.Nat.Nat

  Term: 
        ?{hole_0} ≈ pat n : Prelude.Nat.Nat .
                      ?{hole_1} ≈ ? {hole_3} . {hole_3} . {hole_1} .
          {hole_0}

The ns above the lines show the context of the holes on the right hand side - they include the variable n that is an argument!

patTy is a binding form in Idris's core language that introduces a pattern variable. The idea is that the left-hand side and right-hand side of each pattern should have the same type. Because pattern variables may occur multiple times on either side of the equation, we can achieve this by documenting their types with a binding form that wraps each side. This new binding form is why an "attack" was necessary prior to elaborating the RHS.

patTy is a type former, and pat is the corresponding introduction form. So you can think of patTy as being a bit like a dependent function type, and pat as being a bit like lambda, except they don't introduce functions (they instead are used for pattern-matching definitions).

More Complicated Example
------------------------

This example does not introduce any new notation but the extra complexity gives a more realistic idea of how it is used. Here we start with this file:

.. code-block:: idris

  %language ElabReflection

  testFn : (n : Nat) -> (n = plus n Z) -> (S n = S (plus n Z))
  testFn k ih = %runElab (do debug {a = ()})

when loaded gives:

.. code-block:: idris

  Holes:
        k : Prelude.Nat.Nat
        ih : = Prelude.Nat.Nat Prelude.Nat.Nat k
               (Prelude.Nat.plus k Prelude.Nat.Z)
        ----------------------------------
        {hole_4} : = Prelude.Nat.Nat Prelude.Nat.Nat (Prelude.Nat.S k)
                     (Prelude.Nat.S (Prelude.Nat.plus k Prelude.Nat.Z))

        k : Prelude.Nat.Nat
        ih : = Prelude.Nat.Nat Prelude.Nat.Nat k
               (Prelude.Nat.plus k Prelude.Nat.Z)
        ----------------------------------
        {hole_2} : = Prelude.Nat.Nat Prelude.Nat.Nat (Prelude.Nat.S k)
                     (Prelude.Nat.S (Prelude.Nat.plus k Prelude.Nat.Z))

        k : Prelude.Nat.Nat
        ----------------------------------
        {hole_1} : patTy ih : = Prelude.Nat.Nat Prelude.Nat.Nat k
                                (Prelude.Nat.plus k Prelude.Nat.Z) .
                     = Prelude.Nat.Nat Prelude.Nat.Nat (Prelude.Nat.S k)
                       (Prelude.Nat.S (Prelude.Nat.plus k Prelude.Nat.Z))

        ----------------------------------
        {hole_0} : patTy k : Prelude.Nat.Nat .
                     patTy ih : = Prelude.Nat.Nat Prelude.Nat.Nat k
                                  (Prelude.Nat.plus k Prelude.Nat.Z) .
                       = Prelude.Nat.Nat Prelude.Nat.Nat (Prelude.Nat.S k)
                         (Prelude.Nat.S (Prelude.Nat.plus k Prelude.Nat.Z))

  Term: 
        ?{hole_0} ≈ pat k : Prelude.Nat.Nat .
                      ?{hole_1} ≈ pat ih : = Prelude.Nat.Nat Prelude.Nat.Nat k
                                             (Prelude.Nat.plus k Prelude.Nat.Z) .
                                    ?{hole_2} ≈ ? {hole_4} . {hole_4} . {hole_2} .
                        {hole_1} .
          {hole_0}

.. target-notes::
.. _`Dependently Typed Functional Programs and their Proofs by McBride 1999`: https://www.era.lib.ed.ac.uk/handle/1842/374
