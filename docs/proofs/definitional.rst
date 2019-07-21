In order to understand how to write proofs in Idris I think its worth clarifying some fundamentals, such as,

-  Propositions and judgments
-  Boolean and constructive logic
-  Curry-Howard correspondence
-  Definitional and propositional equalities
-  Axiomatic and constructive approaches

Propositions and Judgments
==========================

Propositions are the subject of our proofs, before the proof then we can't formally say if they are true or not. If the proof is successful then the result is a 'judgment'.
For instance, if the ``proposition`` is,

+-------+
| 1+1=2 |
+-------+

When we prove it, the ``judgment`` is,

+------------+
| 1+1=2 true |
+------------+

Or if the ``proposition`` is,

+-------+
| 1+1=3 |
+-------+

Obviously  we can't prove it is true, but it is still a valid proposition and perhaps we can prove it is false so the ``judgment`` is, 

+-------------+
| 1+1=3 false |
+-------------+

This may seem a bit pedantic but it is important to be careful,  in mathematics not every proposition is true or false for instance, a proposition may be unproven or even unprovable.

So the logic here is different from the logic that comes from boolean algebra. In that case what is not true is false and what is not false is true. The logic we are using here does not have this 'law of excluded middle' so we have to be careful not to use it.

A false proposition is taken to be a contradiction and if we have a contradiction then we can prove anything, so we need to avoid this. Some languages, used in proof assistants, prevent contradictions but such languages cannot be Turing complete, so Idris does not prevent contradictions.

The logic we are using  is called constructive (or sometimes intuitional) because we are constructing a 'database' of judgments.

There are also many other types of logic, another important type of logic for Idris programmers is '``linear logic``' but that's not discussed on this page.

Curry-Howard correspondence
===========================

So how to we relate these proofs to Idris programs? It turns out that there is a correspondence between constructive logic and type theory. They are the same structure and we can switch backward and forward between the two notations because they are the same thing.

The way that this works is that a  proposition is a type so this,

.. code-block:: idris

   Idris> 1+1=2
   2 = 2 : Type

is a proposition and it is also a type. This is built into Idris so when an '=' equals sign appears in a function type an equality type is generated. The following will also produce an equality type:


.. code-block:: idris

   Idris> 1+1=3
   2 = 3 : Type

Both of these are valid propositions so both are valid equality types. But how do we represent true judgment, that is, how do we denote 1+1=2 is true but not 1+1=3.
A type that is true is inhabited, that is, it can be constructed. An equality type has only one constructor 'Refl' so a proof of 1+1=2 is

.. code-block:: idris

   onePlusOne : 1+1=2
   onePlusOne = Refl

So how can Refl, which is a constructor without any parameters, construct an equality type? If we type it on its own then it can't:

.. code-block:: idris

  Idris> Refl
  (input):Can't infer argument A to Refl, Can't infer argument x to Refl

So it must pattern match on its return type:

.. code-block:: idris

    Idris> the (1=1) Refl
    Refl : 1 = 1

So now that we can represent propositions as types other aspects of propositional logic can also be translated to types as follows:

+----------+-------------------+--------------------------+
|          | propositions      | example of possible type |
+----------+-------------------+--------------------------+
| A        | x=y               |                          |
+----------+-------------------+--------------------------+
| B        | y=z               |                          |
+----------+-------------------+--------------------------+
| and      | A /\ B            | Pair(x=y,y=z)            |
+----------+-------------------+--------------------------+
| or       | A \/ B            | Either(x=y,y=z)          |
+----------+-------------------+--------------------------+
| implies  | A -> B            | (x=y) -> (y=x)           |
+----------+-------------------+--------------------------+
| for all  | y=z               |                          |
+----------+-------------------+--------------------------+
| exists   | y=z               |                          |
+----------+-------------------+--------------------------+


And (conjunction)
-----------------

We can have a type which corresponds to conjunction:

.. code-block:: idris

   AndIntro : a -> b -> A a b

There is a built in type called 'Pair'.

Or (disjunction)
----------------

We can have a type which corresponds to disjunction:

.. code-block:: idris

   data Or : Type -> Type -> Type where
   OrIntroLeft : a -> A a b
   OrIntroRight : b -> A a b

There is a built in type called 'Either'.

Definitional and Propositional Equalities
=========================================

We have seen that  we can 'prove' a type by finding a way to construct a term. In the case of equality types there is only one constructor which is 'Refl'.
We have also seen that each side of the equation does not have to be identical like '2=2'. It is enough that both sides are ``definitionaly equal`` like this:

.. code-block:: idris

   onePlusOne : 1+1=2
   onePlusOne = Refl

So both sides of this equation nomalise to 2 and so Refl will type match and the proposition is proved.

We don't have to stick to terms, can also use symbolic parameters so the following  will compile:

.. code-block:: idris

   varIdentity : m = m
   varIdentity = Refl

If a proposition/equality type is not definitionaly equal but is still true then it is ``propositionaly equal``. In this case we may still be able to prove it but some steps in the proof may require us to add something into the terms or at least to take some sideways steps to get to a proof.

Especially when working with equalities containing variable terms (inside functions) it can be hard to know which equality types are definitially equal, in this example plusReducesL is '``definitially equal``' but plusReducesR is not (although it is '``propositionaly equal``'). The only difference between them is the order of the operands.

.. code-block:: idris

   plusReducesL : (n:Nat) -> plus Z n = n
   plusReducesL n = Refl

   plusReducesR : (n:Nat) -> plus n Z = n
   plusReducesR n = Refl

plusReducesR gives the following error:


.. code-block:: idris

   - + Errors (1)
   `-- proof.idr line 6 col 17:
     When checking right hand side of plusReducesR with expected type
             plus n 0 = n

     Type mismatch between
             n = n (Type of Refl)
     and
             plus n 0 = n (Expected type)

     Specifically:
             Type mismatch between
                     n
             and
                     plus n 0

So why is 'Refl' able to prove some equality types but not others?

The first answer is that 'plus' is defined in such a way that it splits on its first argument so it is simple to prove when 0 is the first argument but not the second. So what is the general way to know if Refl will work?

If an equality type can be proved/constructed by using Refl alone it is known as a ``definitional equality``. In order to be definitinally equal both sides of the equation must normalise to unique values. That is, each step in the proof must reduce the term so each step is effectively forced.

So when we type 1+1 in Idris it is immediately converted to 2 because definitional equality is built in.

.. code-block:: idris

    Idris> 1+1
    2 : Integer

In the following pages we discuss how to resolve propositionaly equalies.

Axiomatic and Constructive Approaches
=====================================

How should we define types so that  we can do proofs on them? In the natural numbers with plus example we could have started by treating it as a group based on the plus operator. So we have axioms:

-  for all x,y : ``x+y=y+x``
-  for all x: ``x + 0 = x = 0 + x``
-  for all x,y,z: ``(x + y) + z = x + (x + z)``

Then we can implement '+' so that it respects these axioms (presumably implemented in hardware).

These are axioms, that is a propositions/types that are asserted to be true without proof. In Idris we can use the 'postulate' keyword 


.. code-block:: idris

   commutePlus ``postulate``: x -> y -> plus x y = plus y x

Alternatively we could define the natural numbers based on Zero and Successor. The axioms above then become derived rules and we also gain the ability to do inductive proofs.

As we know, Idris uses both of these approaches with automatic coercion between them which gives the best of both worlds.

So what can we learn from this to implement out own types:

-  Should we try to implement both approaches?
-  Should we define our types by constructing up from primitive types?

Proof theory affects these design decisions.


