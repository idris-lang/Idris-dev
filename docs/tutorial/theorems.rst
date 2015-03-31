.. _sect-theorems:

===============
Theorem Proving
===============

Equality
--------

Idris allows propositional equalities to be declared, allowing theorems about
programs to be stated and proved. Equality is built in, but conceptually
has the following definition:

.. code-block:: idris

    data (=) : a -> b -> Type where
       Refl : x = x

Equalities can be proposed between any values of any types, but the only
way to construct a proof of equality is if values actually are equal.
For example:

.. code-block:: idris

    fiveIsFive : 5 = 5
    fiveIsFive = Refl

    twoPlusTwo : 2 + 2 = 4
    twoPlusTwo = Refl

.. _sect-empty:

The Empty Type
--------------

There is an empty type, :math:`\bot`, which has no constructors. It is
therefore impossible to construct an element of the empty type, at least
without using a partially defined or general recursive function (see
Section :ref:`sect-totality` for more details). We can therefore use the
empty type to prove that something is impossible, for example zero is
never equal to a successor:

.. code-block:: idris

    disjoint : (n : Nat) -> Z = S n -> Void
    disjoint n p = replace {P = disjointTy} p ()
      where
        disjointTy : Nat -> Type
        disjointTy Z = ()
        disjointTy (S k) = Void

There is no need to worry too much about how this function works —
essentially, it applies the library function ``replace``, which uses an
equality proof to transform a predicate. Here we use it to transform a
value of a type which can exist, the empty tuple, to a value of a type
which can’t, by using a proof of something which can’t exist.

Once we have an element of the empty type, we can prove anything.
``void`` is defined in the library, to assist with proofs by
contradiction.

.. code-block:: idris

    void : Void -> a

Simple Theorems
---------------

When type checking dependent types, the type itself gets *normalised*.
So imagine we want to prove the following theorem about the reduction
behaviour of ``plus``:

.. code-block:: idris

    plusReduces : (n:Nat) -> plus Z n = n

We’ve written down the statement of the theorem as a type, in just the
same way as we would write the type of a program. In fact there is no
real distinction between proofs and programs. A proof, as far as we are
concerned here, is merely a program with a precise enough type to
guarantee a particular property of interest.

We won’t go into details here, but the Curry-Howard correspondence [1]_
explains this relationship. The proof itself is trivial, because
``plus Z n`` normalises to ``n`` by the definition of ``plus``:

.. code-block:: idris

    plusReduces n = Refl

It is slightly harder if we try the arguments the other way, because
plus is defined by recursion on its first argument. The proof also works
by recursion on the first argument to ``plus``, namely ``n``.

.. code-block:: idris

    plusReducesZ : (n:Nat) -> n = plus n Z
    plusReducesZ Z = Refl
    plusReducesZ (S k) = cong (plusReducesZ k)

``cong`` is a function defined in the library which states that equality
respects function application:

.. code-block:: idris

    cong : {f : t -> u} -> a = b -> f a = f b

We can do the same for the reduction behaviour of plus on successors:

.. code-block:: idris

    plusReducesS : (n:Nat) -> (m:Nat) -> S (plus n m) = plus n (S m)
    plusReducesS Z m = Refl
    plusReducesS (S k) m = cong (plusReducesS k m)

Even for trival theorems like these, the proofs are a little tricky to
construct in one go. When things get even slightly more complicated, it
becomes too much to think about to construct proofs in this ‘batch
mode’. 

Idris provides interactive editing capabilities, which can help with
building proofs. For more details on building proofs interactively in
an editor, see :ref:`proofs-index`. In the rest of this section, we discuss
Idris's interactive proof mode.

Interactive theorem proving
---------------------------

Instead of writing the proof in one go, we can use Idris’s interactive proof
mode. To do this, we write the general *structure* of the proof, and use
the interactive mode to complete the details. We’ll be constructing the
proof by *induction*, so we write the cases for ``Z`` and ``S``, with a
recursive call in the ``S`` case giving the inductive hypothesis, and
insert *metavariables* for the rest of the definition:

.. code-block:: idris

    plusReducesZ' : (n:Nat) -> n = plus n Z
    plusReducesZ' Z     = ?plusredZ_Z
    plusReducesZ' (S k) = let ih = plusReducesZ' k in
                          ?plusredZ_S

On running , two global names are created, ``plusredZ_Z`` and
``plusredZ_S``, with no definition. We can use the ``:m`` command at the
prompt to find out which metavariables are still to be solved (or, more
precisely, which functions exist but have no definitions), then the
``:t`` command to see their types:

.. code-block:: idris

    *theorems> :m
    Global metavariables:
            [plusredZ_S,plusredZ_Z]

.. code-block:: idris

    *theorems> :t plusredZ_Z
    plusredZ_Z : Z = plus Z Z

    *theorems> :t plusredZ_S
    plusredZ_S : (k : Nat) -> (k = plus k Z) -> S k = plus (S k) Z

The ``:p`` command enters interactive proof mode, which can be used to
complete the missing definitions.

.. code-block:: idris

    *theorems> :p plusredZ_Z

    ---------------------------------- (plusredZ_Z) --------
    {hole0} : Z = plus Z Z

This gives us a list of premises (above the line; there are none here)
and the current goal (below the line; named ``{hole0}`` here). At the
prompt we can enter tactics to direct the construction of the proof. In
this case, we can normalise the goal with the ``compute`` tactic:

.. code-block:: idris

    -plusredZ_Z> compute

    ---------------------------------- (plusredZ_Z) --------
    {hole0} : Z = Z

Now we have to prove that ``Z`` equals ``Z``, which is easy to prove by
``Refl``. To apply a function, such as ``Refl``, we use ``refine`` which
introduces subgoals for each of the function’s explicit arguments
(``Refl`` has none):

.. code-block:: idris

    -plusredZ_Z> refine Refl
    plusredZ_Z: no more goals

Here, we could also have used the ``trivial`` tactic, which tries to
refine by ``Refl``, and if that fails, tries to refine by each name in
the local context. When a proof is complete, we use the ``qed`` tactic
to add the proof to the global context, and remove the metavariable from
the unsolved metavariables list. This also outputs a trace of the proof:

.. code-block:: idris

    -plusredZ_Z> qed
    plusredZ_Z = proof
        compute
        refine Refl

.. code-block:: idris

    *theorems> :m
    Global metavariables:
            [plusredZ_S]

The ``:addproof`` command, at the interactive prompt, will add the proof
to the source file (effectively in an appendix). Let us now prove the
other required lemma, ``plusredZ_S``:

.. code-block:: idris

    *theorems> :p plusredZ_S

    ---------------------------------- (plusredZ_S) --------
    {hole0} : (k : Nat) -> (k = plus k Z) -> S k = plus (S k) Z

In this case, the goal is a function type, using ``k`` (the argument
accessible by pattern matching) and ``ih`` — the local variable
containing the result of the recursive call. We can introduce these as
premisses using the ``intro`` tactic twice (or ``intros``, which
introduces all arguments as premisses). This gives:

.. code-block:: idris

      k : Nat
      ih : k = plus k Z
    ---------------------------------- (plusredZ_S) --------
    {hole2} : S k = plus (S k) Z

Since plus is defined by recursion on its first argument, the term
``plus (S k) Z`` in the goal can be simplified, so we use ``compute``.

.. code-block:: idris

      k : Nat
      ih : k = plus k Z
    ---------------------------------- (plusredZ_S) --------
    {hole2} : S k = S (plus k Z)

We know, from the type of ``ih``, that ``k = plus k Z``, so we would
like to use this knowledge to replace ``plus k Z`` in the goal with
``k``. We can achieve this with the ``rewrite`` tactic:

.. code-block:: idris

    -plusredZ_S> rewrite ih

      k : Nat
      ih : k = plus k Z
    ---------------------------------- (plusredZ_S) --------
    {hole3} : S k = S k

    -plusredZ_S>

The ``rewrite`` tactic takes an equality proof as an argument, and tries
to rewrite the goal using that proof. Here, it results in an equality
which is trivially provable:

.. code-block:: idris

    -plusredZ_S> trivial
    plusredZ_S: no more goals
    -plusredZ_S> qed
    plusredZ_S = proof {
        intros;
        rewrite ih;
        trivial;
    }

Again, we can add this proof to the end of our source file using the
``:addproof`` command at the interactive prompt.

.. _sect-totality:

Totality Checking
-----------------

If we really want to trust our proofs, it is important that they are
defined by *total* functions — that is, a function which is defined for
all possible inputs and is guaranteed to terminate. Otherwise we could
construct an element of the empty type, from which we could prove
anything:

.. code-block:: idris

    -- making use of 'hd' being partially defined
    empty1 : Void
    empty1 = hd [] where
        hd : List a -> a
        hd (x :: xs) = x

    -- not terminating
    empty2 : Void
    empty2 = empty2

Internally, Idris checks every definition for totality, and we can check at
the prompt with the ``:total`` command. We see that neither of the above
definitions is total:

::

    *theorems> :total empty1
    possibly not total due to: empty1#hd
        not total as there are missing cases
    *theorems> :total empty2
    possibly not total due to recursive path empty2

Note the use of the word “possibly” — a totality check can, of course,
never be certain due to the undecidability of the halting problem. The
check is, therefore, conservative. It is also possible (and indeed
advisable, in the case of proofs) to mark functions as total so that it
will be a compile time error for the totality check to fail:

.. code-block:: idris

    total empty2 : Void
    empty2 = empty2

::

    Type checking ./theorems.idr
    theorems.idr:25:empty2 is possibly not total due to recursive path empty2

Reassuringly, our proof in Section :ref:`sect-empty` that the zero and
successor constructors are disjoint is total:

.. code-block:: idris

    *theorems> :total disjoint
    Total

The totality check is, necessarily, conservative. To be recorded as
total, a function ``f`` must:

-  Cover all possible inputs

-  Be *well-founded* — i.e. by the time a sequence of (possibly
   mutually) recursive calls reaches ``f`` again, it must be possible to
   show that one of its arguments has decreased.

-  Not use any data types which are not *strictly positive*

-  Not call any non-total functions

Directives and Compiler Flags for Totality
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

By default, Idris allows all well-typed definitions, whether total or not.
However, it is desirable for functions to be total as far as possible, as this
provides a guarantee that they provide a result for all possible inputs, in
finite time. It is possible to make total functions a requirement, either:

-  By using the ``--total`` compiler flag.

-  By adding a ``%default total`` directive to a source file. All
   definitions after this will be required to be total, unless
   explicitly flagged as ``partial``.

All functions *after* a ``%default total`` declaration are required to
be total. Correspondingly, after a ``%default partial`` declaration, the
requirement is relaxed.

Finally, the compiler flag ``--warnpartial`` causes to print a warning
for any undeclared partial function.

Totality checking issues
~~~~~~~~~~~~~~~~~~~~~~~~

Please note that the totality checker is not perfect! Firstly, it is
necessarily conservative due to the undecidability of the halting
problem, so many programs which *are* total will not be detected as
such. Secondly, the current implementation has had limited effort put
into it so far, so there may still be cases where it believes a function
is total which is not. Do not rely on it for your proofs yet!

Hints for totality
~~~~~~~~~~~~~~~~~~

In cases where you believe a program is total, but Idris does not agree, it is
possible to give hints to the checker to give more detail for a termination
argument. The checker works by ensuring that all chains of recursive calls
eventually lead to one of the arguments decreasing towards a base case, but
sometimes this is hard to spot. For example, the following definition cannot be
checked as ``total`` because the checker cannot decide that ``filter (<= x) xs`` 
will always be smaller than ``(x :: xs)``:

.. code-block:: idris

    qsort : Ord a => List a -> List a
    qsort [] = []
    qsort (x :: xs)
       = qsort (filter (< x) xs) ++
          (x :: qsort (filter (>= x) xs))

The function ``assert_smaller``, defined in the Prelude, is intended to
address this problem:

.. code-block:: idris

    assert_smaller : a -> a -> a
    assert_smaller x y = y

It simply evaluates to its second argument, but also asserts to the
totality checker that ``y`` is structurally smaller than ``x``. This can
be used to explain the reasoning for totality if the checker cannot work
it out itself. The above example can now be written as:

.. code-block:: idris

    total
    qsort : Ord a => List a -> List a
    qsort [] = []
    qsort (x :: xs)
       = qsort (assert_smaller (x :: xs) (filter (< x) xs)) ++
          (x :: qsort (assert_smaller (x :: xs) (filter (>= x) xs)))

The expression ``assert_smaller (x :: xs) (filter (<= x) xs)`` asserts
that the result of the filter will always be smaller than the pattern
``(x :: xs)``.

In more extreme cases, the function ``assert_total`` marks a
subexpression as always being total:

.. code-block:: idris

    assert_total : a -> a
    assert_total x = x

In general, this function should be avoided, but it can be very useful
when reasoning about primitives or externally defined functions (for
example from a C library) where totality can be shown by an external
argument.


.. [1] Timothy G. Griffin. 1989. A formulae-as-type notion of
       control. In Proceedings of the 17th ACM SIGPLAN-SIGACT
       symposium on Principles of programming languages (POPL
       '90). ACM, New York, NY, USA, 47-58. DOI=10.1145/96709.96714
       http://doi.acm.org/10.1145/96709.96714
