***************************************
DEPRECATED: Interactive Theorem Proving
***************************************

.. warning::
   The interactive theorem-proving interface documented here has been
   deprecated in favor of :ref:`elaborator-reflection`.

Idris also supports interactive theorem proving via tactics. This
is generally not recommended to be used directly, but rather used as a
mechanism for building proof automation which is beyond the scope of this
tutorial. In this section, we briefly discus tactics.

One way to write proofs interactively is to write the general *structure* of
the proof, and use the interactive mode to complete the details.
Consider the following definition, proved in :ref:`sect-theorems`:

.. code-block:: idris

    plusReduces : (n:Nat) -> plus Z n = n

We’ll be constructing the proof by *induction*, so we write the cases for ``Z``
and ``S``, with a recursive call in the ``S`` case giving the inductive
hypothesis, and insert *holes* for the rest of the definition:

.. code-block:: idris

    plusReducesZ' : (n:Nat) -> n = plus n Z
    plusReducesZ' Z     = ?plusredZ_Z
    plusReducesZ' (S k) = let ih = plusReducesZ' k in
                          ?plusredZ_S

On running , two global names are created, ``plusredZ_Z`` and
``plusredZ_S``, with no definition. We can use the ``:m`` command at the
prompt to find out which holes are still to be solved (or, more
precisely, which functions exist but have no definitions), then the
``:t`` command to see their types:

.. code-block:: idris

    *theorems> :m
    Global holes:
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
to add the proof to the global context, and remove the hole from the
unsolved holes list. This also outputs a trace of the proof:

.. code-block:: idris

    -plusredZ_Z> qed
    plusredZ_Z = proof
        compute
        refine Refl

.. code-block:: idris

    *theorems> :m
    Global holes:
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
premises using the ``intro`` tactic twice (or ``intros``, which
introduces all arguments as premises). This gives:

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
