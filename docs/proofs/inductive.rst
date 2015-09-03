****************
Inductive Proofs
****************

Before embarking on proving ``plus_commutes`` in Idris itself, let us
consider the overall structure of a proof of some property of natural
numbers. Recall that they are defined recursively, as follows:

.. code-block:: idris

    data Nat : Type where
         Z : Nat
         S : Nat -> Nat

A *total* function over natural numbers must both terminate, and cover
all possible inputs. Idris checks functions for totality by checking that
all inputs are covered, and that all recursive calls are on
*structurally smaller* values (so recursion will always reach a base
case). Recalling ``plus``:

.. code-block:: idris

    plus : Nat -> Nat -> Nat
    plus Z     m = m
    plus (S k) m = S (plus k m)

This is total because it covers all possible inputs (the first argument
can only be ``Z`` or ``S k`` for some ``k``, and the second argument
``m`` covers all possible ``Nat``) and in the recursive call, ``k``
is structurally smaller than ``S k`` so the first argument will always
reach the base case ``Z`` in any sequence of recursive calls.

In some sense, this resembles a mathematical proof by induction (and
this is no coincidence!). For some property ``P`` of a natural number
``x``, we can show that ``P`` holds for all ``x`` if:

-  ``P`` holds for zero (the base case).

-  Assuming that ``P`` holds for ``k``, we can show ``P`` also holds for
   ``S k`` (the inductive step).

In ``plus``, the property we are trying to show is somewhat trivial (for
all natural numbers ``x``, there is a ``Nat`` which need not have any
relation to ``x``). However, it still takes the form of a base case and
an inductive step. In the base case, we show that there is a ``Nat``
arising from ``plus n m`` when ``n = Z``, and in the inductive step we
show that there is a ``Nat`` arising when ``n = S k`` and we know we can
get a ``Nat`` inductively from ``plus k m``. We could even write a
function capturing all such inductive definitions:

.. code-block:: idris

    nat_induction : (P : Nat -> Type) ->             -- Property to show
                    (P Z) ->                         -- Base case
                    ((k : Nat) -> P k -> P (S k)) -> -- Inductive step
                    (x : Nat) ->                     -- Show for all x
                    P x
    nat_induction P p_Z p_S Z = p_Z
    nat_induction P p_Z p_S (S k) = p_S k (nat_induction P p_Z p_S k)

Using ``nat_induction``, we can implement an equivalent inductive
version of ``plus``:

.. code-block:: idris

    plus_ind : Nat -> Nat -> Nat
    plus_ind n m
       = nat_induction (\x => Nat)
                       m                      -- Base case, plus_ind Z m
                       (\k, k_rec => S k_rec) -- Inductive step plus_ind (S k) m
                                              -- where k_rec = plus_ind k m
                       n

To prove that ``plus n m = plus m n`` for all natural numbers ``n`` and
``m``, we can also use induction. Either we can fix ``m`` and perform
induction on ``n``, or vice versa. We can sketch an outline of a proof;
performing induction on ``n``, we have:

-  Property ``P`` is ``\x => plus x m = plus m x``.

-  Show that ``P`` holds in the base case and inductive step:

   -  | Base case: ``P Z``, i.e.
      | ``plus Z m = plus m Z``, which reduces to
      | ``m = plus m Z`` due to the definition of ``plus``.

   -  | Inductive step: Inductively, we know that ``P k`` holds for a specific, fixed ``k``, i.e.
      | ``plus k m = plus m k`` (the induction hypothesis). Given this, show ``P (S k)``, i.e.
      | ``plus (S k) m = plus m (S k)``, which reduces to
      | ``S (plus k m) = plus m (S k)``. From the induction hypothesis, we can rewrite this to
      | ``S (plus m k) = plus m (S k)``.

To complete the proof we therefore need to show that ``m = plus m Z``
for all natural numbers ``m``, and that ``S (plus m k) = plus m (S k)``
for all natural numbers ``m`` and ``k``. Each of these can also be
proved by induction, this time on ``m``.

We are now ready to embark on a proof of commutativity of ``plus``
formally in Idris.
