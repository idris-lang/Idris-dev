.. _sect-provisional:

***********************
Provisional Definitions
***********************

Sometimes when programming with dependent types, the type required by
the type checker and the type of the program we have written will be
different (in that they do not have the same normal form), but
nevertheless provably equal. For example, recall the ``parity``
function:

.. code-block:: idris

    data Parity : Nat -> Type where
       Even : Parity (n + n)
       Odd  : Parity (S (n + n))

We’d like to implement this as follows:

.. code-block:: idris

    parity : (n:Nat) -> Parity n
    parity Z     = Even {n=Z}
    parity (S Z) = Odd {n=Z}
    parity (S (S k)) with (parity k)
      parity (S (S (j + j)))     | Even = Even {n=S j}
      parity (S (S (S (j + j)))) | Odd  = Odd {n=S j}

This simply states that zero is even, one is odd, and recursively, the
parity of ``k+2`` is the same as the parity of ``k``. Explicitly marking
the value of ``n`` is even and odd is necessary to help type inference.
Unfortunately, the type checker rejects this:

::

    viewsbroken.idr:12:10:When elaborating right hand side of ViewsBroken.parity:
    Type mismatch between 
        Parity (plus (S j) (S j))
    and
        Parity (S (S (plus j j)))

    Specifically:
        Type mismatch between
            plus (S j) (S j)
        and
            S (S (plus j j))

The type checker is telling us that ``(j+1)+(j+1)`` and ``2+j+j`` do not
normalise to the same value. This is because ``plus`` is defined by
recursion on its first argument, and in the second value, there is a
successor symbol on the second argument, so this will not help with
reduction. These values are obviously equal — how can we rewrite the
program to fix this problem?

Provisional definitions
=======================

*Provisional definitions* help with this problem by allowing us to defer
the proof details until a later point. There are two main reasons why
they are useful.

-  When *prototyping*, it is useful to be able to test programs before
   finishing all the details of proofs.

-  When *reading* a program, it is often much clearer to defer the proof
   details so that they do not distract the reader from the underlying
   algorithm.

Provisional definitions are written in the same way as ordinary
definitions, except that they introduce the right hand side with a
``?=`` rather than ``=``. We define ``parity`` as follows:

.. code-block:: idris

    parity : (n:Nat) -> Parity n
    parity Z = Even {n=Z}
    parity (S Z) = Odd {n=Z}
    parity (S (S k)) with (parity k)
      parity (S (S (j + j))) | Even ?= Even {n=S j}
      parity (S (S (S (j + j)))) | Odd ?= Odd {n=S j}

When written in this form, instead of reporting a type error, Idris
will insert a hole standing for a theorem which will correct the
type error. Idris tells us we have two proof obligations, with names
generated from the module and function names:

.. code-block:: idris

    *views> :m
    Global holes:
            [views.parity_lemma_2,views.parity_lemma_1]

The first of these has the following type:

.. code-block:: idris

    *views> :p views.parity_lemma_1

    ---------------------------------- (views.parity_lemma_1) --------
    {hole0} : (j : Nat) -> (Parity (plus (S j) (S j))) -> Parity (S (S (plus j j)))

    -views.parity_lemma_1>

The two arguments are ``j``, the variable in scope from the pattern
match, and ``value``, which is the value we gave in the right hand side
of the provisional definition. Our goal is to rewrite the type so that
we can use this value. We can achieve this using the following theorem
from the prelude:

.. code-block:: idris

    plusSuccRightSucc : (left : Nat) -> (right : Nat) ->
      S (left + right) = left + (S right)

We need to use ``compute`` again to unfold the definition of ``plus``:

.. code-block:: idris

    -views.parity_lemma_1> compute


    ---------------------------------- (views.parity_lemma_1) --------
    {hole0} : (j : Nat) -> (Parity (S (plus j (S j)))) -> Parity (S (S (plus j j)))

After applying ``intros`` we have:

.. code-block:: idris

    -views.parity_lemma_1> intros

      j : Nat
      value : Parity (S (plus j (S j)))
    ---------------------------------- (views.parity_lemma_1) --------
    {hole2} : Parity (S (S (plus j j)))

Then we apply the ``plusSuccRightSucc`` rewrite rule, symmetrically, to
``j`` and ``j``, giving:

.. code-block:: idris

    -views.parity_lemma_1> rewrite sym (plusSuccRightSucc j j)

      j : Nat
      value : Parity (S (plus j (S j)))
    ---------------------------------- (views.parity_lemma_1) --------
    {hole3} : Parity (S (plus j (S j)))

``sym`` is a function, defined in the library, which reverses the order
of the rewrite:

.. code-block:: idris

    sym : l = r -> r = l
    sym Refl = Refl

We can complete this proof using the ``trivial`` tactic, which finds
``value`` in the premises. The proof of the second lemma proceeds in
exactly the same way.

We can now test the ``natToBin`` function from Section :ref:`sect-nattobin`
at the prompt. The number 42 is 101010 in binary. The binary digits are
reversed:

.. code-block:: idris

    *views> show (natToBin 42)
    "[False, True, False, True, False, True]" : String

Suspension of Disbelief
=======================

Idris requires that proofs be complete before compiling programs
(although evaluation at the prompt is possible without proof details).
Sometimes, especially when prototyping, it is easier not to have to do
this. It might even be beneficial to test programs before attempting to
prove things about them — if testing finds an error, you know you had
better not waste your time proving something!

Therefore, Idris provides a built-in coercion function, which allows
you to use a value of the incorrect types:

.. code-block:: idris

    believe_me : a -> b

Obviously, this should be used with extreme caution. It is useful when
prototyping, and can also be appropriate when asserting properties of
external code (perhaps in an external C library). The “proof” of
``views.parity_lemma_1`` using this is:

.. code-block:: idris

    views.parity_lemma_2 = proof {
        intro;
        intro;
        exact believe_me value;
    }

The ``exact`` tactic allows us to provide an exact value for the proof.
In this case, we assert that the value we gave was correct.

Example: Binary numbers
=======================

Previously, we implemented conversion to binary numbers using the
``Parity`` view. Here, we show how to use the same view to implement a
verified conversion to binary. We begin by indexing binary numbers over
their ``Nat`` equivalent. This is a common pattern, linking a
representation (in this case ``Binary``) with a meaning (in this case
``Nat``):

.. code-block:: idris

    data Binary : Nat -> Type where
       BEnd : Binary Z
       BO : Binary n -> Binary (n + n)
       BI : Binary n -> Binary (S (n + n))

``BO`` and ``BI`` take a binary number as an argument and effectively
shift it one bit left, adding either a zero or one as the new least
significant bit. The index, ``n + n`` or ``S (n + n)`` states the result
that this left shift then add will have to the meaning of the number.
This will result in a representation with the least significant bit at
the front.

Now a function which converts a Nat to binary will state, in the type,
that the resulting binary number is a faithful representation of the
original Nat:

.. code-block:: idris

    natToBin : (n:Nat) -> Binary n

The ``Parity`` view makes the definition fairly simple — halving the
number is effectively a right shift after all — although we need to use
a provisional definition in the Odd case:

.. code-block:: idris

    natToBin : (n:Nat) -> Binary n
    natToBin Z = BEnd
    natToBin (S k) with (parity k)
       natToBin (S (j + j))     | Even  = BI (natToBin j)
       natToBin (S (S (j + j))) | Odd  ?= BO (natToBin (S j))

The problem with the Odd case is the same as in the definition of
``parity``, and the proof proceeds in the same way:

.. code-block:: idris

    natToBin_lemma_1 = proof {
        intro;
        intro;
        rewrite sym (plusSuccRightSucc j j);
        trivial;
    }

To finish, we’ll implement a main program which reads an integer from
the user and outputs it in binary.

.. code-block:: idris

    main : IO ()
    main = do putStr "Enter a number: "
              x <- getLine
              print (natToBin (fromInteger (cast x)))

For this to work, of course, we need a ``Show`` implementation for
``Binary n``:

.. code-block:: idris

    Show (Binary n) where
        show (BO x) = show x ++ "0"
        show (BI x) = show x ++ "1"
        show BEnd = ""
