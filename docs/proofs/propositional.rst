This page attempts to explain some of the techniques used in Idris to prove propositional equalities.

Proving Propositional Equality
==============================

We have seen that definitional equalities can be proved using Refl since they always normalise to unique values that can be compared directly.

However with propositional equalities we are using symbolic variables they do not always normalse.

So to take the previous example:

plusReducesR : (n:Nat) -> plus n Z = n

In this case 'plus n Z' does not normalise to n. Even though both sides are equal we cannot pattern match Refl.

If the pattern match cannot match for all 'n' then the way around this is to separately match all possible values of 'n'. In the case of natural numbers we do this by induction.

So here:

.. code-block:: idris

   plusReducesR : n = plus n 0
   plusReducesR {n = Z} = Refl
   plusReducesR {n = (S k)} = let rec = plus_commutes_Z {n=k} in
                                  rewrite rec in Refl

we don't call Refl to match on 'n = plus n 0' forall 'n' we call it for every number separately. So, in the second line, the pattern matcher knows to substitute Z for n in the type being matched. This uses 'rewrite' which is explained below.

Replace
=======

This implements the 'indiscernability of identicals' principle, if two terms are equal then they have the same properties. In other words, if x=y, then we can substitute y for x in any expression. In our proofs we can express this as:

   if x=y
   then P x = P y

where P is a pure function representing the property. In the examples below P is an expression in some variable with a type like this: P: n -> Type

So if n is a natural number variable then P could be something like 2*n + 3.

To use this in our proofs there is the following function in the prelude:

.. code-block:: idris

   ||| Perform substitution in a term according to some equality.
   replace : {a:_} -> {x:_} -> {y:_} -> {P : a -> Type} -> x = y -> P x -> P y
   replace Refl prf = prf

Removing the implicits, if we supply an equality (x=y) and a proof of a property of x (P x) then we get a proof of a property of y (P y)

.. code-block:: idris

   > :t replace
   replace : (x = y) -> P x -> P y

So, in the following example, if we supply p1 x which is a proof that x=2 and the equality x=y then we get a proof that y=2.

.. code-block:: idris

   p1: Nat -> Type
   p1 n = (n=2)

   testReplace: (x=y) -> (p1 x) -> (p1 y)
   testReplace a b = replace a b

Rewrite
=======

Similar to 'replace' above but Idris provides a nicer syntax which makes 'rewrite' easier to use in examples like plusReducesR above.

.. code-block:: idris

   rewrite__impl : (P : a -> Type) -> x = y -> P y -> P x
   rewrite__impl p Refl prf = prf

The difference from 'replace' above is nicer syntax and the property p1 is explicitly supplied and it goes in the opposite direction (input and output reversed).

Example: again we supply p1 which is a proof that x=2 and the equality x=y then we get a proof that y=2.

.. code-block:: idris

   p1: Nat -> Type
   p1 x = (x=2)

   testRewrite2: (x=y) -> (p1 y) -> (p1 x)
   testRewrite2 a b = rewrite a in b

We can think of rewrite doing this:

 * Start with a equation x=y and a property P: x -> Type
 * Searches y in P
 * Replaces all occurrences of y with x in P.

That is, we are doing a substitution.

Symmetry and Transitivity
=========================

In addition to 'reflexivity' equality also obeys 'symmetry' and 'transitivity' and these are also included in the prelude:

.. code-block:: idris

   ||| Symmetry of propositional equality
   sym : {left:a} -> {right:b} -> left = right -> right = left
   sym Refl = Refl

   ||| Transitivity of propositional equality
   trans : {a:x} -> {b:y} -> {c:z} -> a = b -> b = c -> a = c
   trans Refl Refl = Refl

Heterogeneous Equality
======================

Also included in the prelude: 

.. code-block:: idris

   ||| Explicit heterogeneous ("John Major") equality. Use this when Idris
   ||| incorrectly chooses homogeneous equality for `(=)`.
   ||| @ a the type of the left side
   ||| @ b the type of the right side
   ||| @ x the left side
   ||| @ y the right side
   (~=~) : (x : a) -> (y : b) -> Type
   (~=~) x y = (x = y)



