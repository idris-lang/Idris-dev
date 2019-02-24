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

we don't call Refl to match on 'n = plus n 0' forall 'n' we call it for every number separately. So, in the second line, somehow the pattern matcher knows to substitute Z for n in the type being matched.

Replace
=======

If two terms are equal then they have the same properties. In our proofs we can express this as:

   if x=y
   then P x = P y

where P is a pure function.

To use this in our proofs there is the following function in the prelude: 

.. code-block:: idris

   ||| Perform substitution in a term according to some equality.
   replace : {a:_} -> {x:_} -> {y:_} -> {P : a -> Type} -> x = y -> P x -> P y
   replace Refl prf = prf

Rewrite
=======

Similar to 'replace' above but Idris provides a nicer syntax which makes 'rewrite' easier to use in examples like plusReducesR above.

.. code-block:: idris

   ||| Perform substitution in a term according to some equality.
   |||
   ||| Like `replace`, but with an explicit predicate, and applying the rewrite
   ||| in the other direction, which puts it in a form usable by the `rewrite`
   ||| tactic and term.
   rewrite__impl : (P : a -> Type) -> x = y -> P y -> P x
   rewrite__impl p Refl prf = prf

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



