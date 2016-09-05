********************************************
Running example: Addition of Natural Numbers
********************************************

Throughout this tutorial, we will be working with the following
function, defined in the Idris prelude, which defines addition on
natural numbers:

.. code-block:: idris

    plus : Nat -> Nat -> Nat
    plus Z     m = m
    plus (S k) m = S (plus k m)

It is defined by the above equations, meaning that we have for free the
properties that adding ``m`` to zero always results in ``m``, and that
adding ``m`` to any non-zero number ``S k`` always results in
``S (plus k m)``. We can see this by evaluation at the Idris REPL (i.e.
the prompt, the read-eval-print loop):

.. code-block:: idris

    Idris> \m => plus Z m
    \m => m : Nat -> Nat

    Idris> \k,m => plus (S k) m
    \k => \m => S (plus k m) : Nat -> Nat -> Nat

Note that unlike many other language REPLs, the Idris REPL performs
evaluation on *open* terms, meaning that it can reduce terms which
appear inside lambda bindings, like those above. Therefore, we can
introduce unknowns ``k`` and ``m`` as lambda bindings and see how
``plus`` reduces.

The ``plus`` function has a number of other useful properties, for
example:

-  It is *commutative*, that is for all ``Nat`` inputs ``n`` and ``m``,
   we know that ``plus n m = plus m n``.

-  It is *associative*, that is for all ``Nat`` inputs ``n``, ``m`` and
   ``p``, we know that ``plus n (plus m p) = plus (plus m n) p``.

We can use these properties in an Idris program, but in order to do so
we must *prove* them.

Equality Proofs
===============

Idris has a built-in propositional equality type, conceptually defined
as follows:

.. code-block:: idris

    data (=) : a -> b -> Type where
       Refl : x = x

Note that this must be built-in, rather than defined in the library,
because ``=`` is a reserved operator — you cannot define this directly
in your own code.

It is *propositional* equality, where the type states that any two
values in different types ``a`` and ``b`` may be proposed to be equal.
There is only one way to *prove* equality, however, which is by
reflexivity (``Refl``).

We have a *type* for propositional equality here, and correspondingly a
*program* inhabiting an instance of this type can be seen as a proof of
the corresponding proposition [1]_. So, trivially, we can prove that
``4`` equals ``4``:

.. code-block:: idris

    four_eq : 4 = 4
    four_eq = Refl

However, trying to prove that ``4 = 5`` results in failure:

.. code-block:: idris

    four_eq_five : 4 = 5
    four_eq_five = Refl

The type ``4 = 5`` is a perfectly valid type, but is uninhabited, so
when trying to type check this definition, Idris gives the following
error:

::

    When elaborating right hand side of four_eq_five:
    Type mismatch between
            x = x (Type of Refl)
    and
            4 = 5 (Expected type)

Type checking equality proofs
-----------------------------

An important step in type checking Idris programs is *unification*,
which attempts to resolve implicit arguments such as the implicit
argument ``x`` in ``Refl``. As far as our understanding of type checking
proofs is concerned, it suffices to know that unifying two terms
involves reducing both to normal form then trying to find an assignment
to implicit arguments which will make those normal forms equal.

When type checking ``Refl``, Idris requires that the type is of the form
``x = x``, as we see from the type of ``Refl``. In the case of
``four_eq_five``, Idris will try to unify the expected type ``4 = 5``
with the type of ``Refl``, ``x = x``, notice that a solution requires
that ``x`` be both ``4`` and ``5``, and therefore fail.

Since type checking involves reduction to normal form, we can write the
following equalities directly:

.. code-block:: idris

    twoplustwo_eq_four : 2 + 2 = 4
    twoplustwo_eq_four = Refl

    plus_reduces_Z : (m : Nat) -> plus Z m = m
    plus_reduces_Z m = Refl

    plus_reduces_Sk : (k, m : Nat) -> plus (S k) m = S (plus k m)
    plus_reduces_Sk k m = Refl

Heterogeneous Equality
======================

Equality in Idris is *heterogeneous*, meaning that we can even propose
equalities between values in different types:

.. code-block:: idris

    idris_not_php : 2 = "2"

Obviously, in Idris the type ``2 = "2"`` is uninhabited, and one might
wonder why it is useful to be able to propose equalities between values
in different types. However, with dependent types, such equalities can
arise naturally. For example, if two vectors are equal, their lengths
must be equal:

.. code-block:: idris

    vect_eq_length : (xs : Vect n a) -> (ys : Vect m a) ->
                     (xs = ys) -> n = m

In the above declaration, ``xs`` and ``ys`` have different types because
their lengths are different, but we would still like to draw a
conclusion about the lengths if they happen to be equal. We can define
``vect_eq_length`` as follows:

.. code-block:: idris

    vect_eq_length xs xs Refl = Refl

By matching on ``Refl`` for the third argument, we know that the only
valid value for ``ys`` is ``xs``, because they must be equal, and
therefore their types must be equal, so the lengths must be equal.

Alternatively, we can put an underscore for the second ``xs``, since
there is only one value which will type check:

.. code-block:: idris

    vect_eq_length xs _ Refl = Refl

Properties of ``plus``
======================

Using the ``(=)`` type, we can now state the properties of ``plus``
given above as Idris type declarations:

.. code-block:: idris

    plus_commutes : (n, m : Nat) -> plus n m = plus m n
    plus_assoc : (n, m, p : Nat) -> plus n (plus m p) = plus (plus n m) p

Both of these properties (and many others) are proved for natural number
addition in the Idris standard library, using ``(+)`` from the ``Num``
interface rather than using ``plus`` directly. They have the names
``plusCommutative`` and ``plusAssociative`` respectively.

In the remainder of this tutorial, we will explore several different
ways of proving ``plus_commutes`` (or, to put it another way, writing
the function.) We will also discuss how to use such equality proofs, and
see where the need for them arises in practice.

.. [1]
   This is known as the Curry-Howard correspondence.
