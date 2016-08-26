*************************
Erasure By Usage Analysis
*************************

This work stems from this `feature proposal
<https://github.com/idris-lang/Idris-dev/wiki/Egg-%232%3A-Erasure-annotations>`__
(obsoleted by this page). Beware that the information in the proposal
is out of date — and sometimes even in direct contradiction with the
eventual implementation.

Motivation
==========

Traditional dependently typed languages (Agda, Coq) are good at
erasing *proofs* (either via irrelevance or an extra universe).

.. code-block:: idris

    half : (n : Nat) -> Even n -> Nat
    half Z EZ = Z
    half (S (S n)) (ES pf) = S (half n pf)

For example, in the above snippet, the second argument is a proof,
which is used only to convince the compiler that the function is
total. This proof is never inspected at runtime and thus can be
erased. In this case, the mere existence of the proof is sufficient
and we can use irrelevance-related methods to achieve erasure.

However, sometimes we want to erase *indices* and this is where the
traditional approaches stop being useful, mainly for reasons described
in the `original proposal
<https://github.com/idris-lang/Idris-dev/wiki/Egg-%232%3A-Erasure-annotations>`__.

.. code-block:: idris

    uninterleave : {n : Nat} -> Vect (n * 2) a -> (Vect n a, Vect n a)
    uninterleave [] = ([] , [])
    uninterleave (x :: y :: rest) with (unzipPairs rest)
      | (xs, ys) = (x :: xs, y :: ys)

Notice that in this case, the second argument is the important one and
we would like to get rid of the ``n`` instead, although the shape of
the program is generally the same as in the previous case.

There are methods described by Brady, McBride and McKinna in [BMM04]_
to remove the indices from data structures, exploiting the fact that
functions operating on them either already have a copy of the
appropriate index or the index can be quickly reconstructed if needed.
However, we often want to erase the indices altogether, from the whole
program, even in those cases where reconstruction is not possible.

The following two sections describe two cases where doing so improves
the runtime performance asymptotically.

Binary numbers
--------------

- O(n) instead of O(log n)

Consider the following ``Nat``-indexed type family representing binary
numbers:

.. code-block:: idris

    data Bin : Nat -> Type where
      N : Bin 0
      O : {n : Nat} -> Bin n -> Bin (0 + 2*n)
      I : {n : Nat} -> Bin n -> Bin (1 + 2*n)

These are supposed to be (at least asymptotically) fast and
memory-efficient because their size is logarithmic compared to the
numbers they represent.

Unfortunately this is not the case. The problem is that these binary
numbers still carry the *unary* indices with them, performing
arithmetic on the indices whenever arithmetic is done on the binary
numbers themselves. Hence the real representation of the number 15
looks like this:

::

    I -> I -> I -> I -> N
    S    S    S    Z
    S    S    Z
    S    S
    S    Z
    S
    S
    S
    Z

The used memory is actually *linear*, not logarithmic and therefore we
cannot get below O(n) with time complexities.

One could argue that Idris in fact compiles ``Nat`` via GMP but
that's a moot point for two reasons:

+ First, whenever we try to index our data structures with anything
  else than ``Nat``, the compiler is not going to come to the rescue.

+ Second, even with ``Nat``, the GMP integers are *still* there and
  they slow the runtime down.

This ought not to be the case since the ``Nat`` are never used at
runtime and they are only there for typechecking purposes. Hence we
should get rid of them and get runtime code similar to what a idris
programmer would write.

U-views of lists
----------------

-  O(n^2) instead of O(n)

Consider the type of U-views of lists:

.. code-block:: idris

    data U : List a -> Type where
      nil : U []
      one : (z : a) -> U [z]
      two : {xs : List a} -> (x : a) -> (u : U xs) -> (y : a) -> U (x :: xs ++ [y])

For better intuition, the shape of the U-view of
``[x0,x1,x2,z,y2,y1,y0]`` looks like this:

::

      x0   y0    (two)
      x1   y1    (two)
      x2   y1    (two)
         z       (one)

When recursing over this structure, the values of ``xs`` range over
``[x0,x1,x2,z,y2,y1,y0]``, ``[x1,x2,z,y2,y1]``, ``[x2,z,y2]``,
``[z]``.  No matter whether these lists are stored or built on demand,
they take up a quadratic amount of memory (because they cannot share
nodes), and hence it takes a quadratic amount of time just to build
values of this index alone.

But the reasonable expectation is that operations with U-views take
linear time — so we need to erase the index ``xs`` if we want to
achieve this goal.

Changes to Idris
================

Usage analysis is run at every compilation and its outputs are used
for various purposes. This is actually invisible to the user but it's
a relatively big and important change, which enables the new features.

Everything that is found to be unused is erased. No annotations are
needed, just don't use the thing and it will vanish from the generated
code. However, if you wish, you can use the dot annotations to get a
warning if the thing is accidentally used.

"Being used" in this context means that the value of the "thing" may
influence run-time behaviour of the program. (More precisely, it is
not found to be irrelevant to the run-time behaviour by the usage
analysis algorithm.)

"Things" considered for removal by erasure include:

* function arguments

* data constructor fields (including record fields and dictionary
  fields of interface implementations)

For example, ``Either`` often compiles to the same runtime
representation as ``Bool``. Constructor field removal sometimes
combines with the newtype optimisation to have quite a strong effect.

There is a new compiler option ``--warnreach``, which will enable
warnings coming from erasure. Since we have full usage analysis, we
can compile even those programs that violate erasure annotations --
it's just that the binaries may run slower than expected. The warnings
will be enabled by default in future versions of Idris (and possibly
turned to errors). However, in this transitional period, we chose to
keep them on-demand to avoid confusion until better documentation is
written.

Case-tree elaboration tries to avoid using dotted "things" whenever
possible. (NB. This is not yet perfect and it's being worked on:
https://gist.github.com/ziman/10458331)

Postulates are no longer required to be collapsible. They are now
required to be *unused* instead.

Changes to the language
=======================

You can use dots to mark fields that are not intended to be used at
runtime.

.. code-block:: idris

    data Bin : Nat -> Type where
      N : Bin 0
      O : .{n : Nat} -> Bin n -> Bin (0 + 2*n)
      I : .{n : Nat} -> Bin n -> Bin (1 + 2*n)

If these fields are found to be used at runtime, the dots will trigger
a warning (with ``--warnreach``).

Note that free (unbound) implicits are dotted by default so, for
example, the constructor ``O`` can be defined as:

.. code-block:: idris

      O : Bin n -> Bin (0 + 2*n)

and this is actually the preferred form.

If you have a free implicit which is meant to be used at runtime, you
have to change it into an (undotted) ``{bound : implicit}``.

You can also put dots in types of functions to get more guarantees.

.. code-block:: idris

    half : (n : Nat) -> .(pf : Even n) -> Nat

and free implicits are automatically dotted here, too.

What it means
=============

Dot annotations serve two purposes:

* influence case-tree elaboration to avoid dotted variables

* trigger warnings when a dotted variable is used

However, there's no direct connection between being dotted and being
erased. The compiler erases everything it can, dotted or not. The dots
are there mainly to help the programmer (and the compiler) refrain
from using the values they want to erase.

How to use it
=============

Ideally, few or no extra annotations are needed -- in practice, it
turns out that having free implicits automatically dotted is enough to
get good erasure.

Therefore, just compile with ``--warnreach`` to see warnings if
erasure cannot remove parts of the program.

However, those programs that have been written without runtime
behaviour in mind, will need some help to get in the form that
compiles to a reasonable binary. Generally, it's sufficient to follow
erasure warnings (which may be sometimes unhelpful at the moment).

Benchmarks
==========

-  source: https://github.com/ziman/idris-benchmarks
-  results: http://ziman.functor.sk/erasure-bm/

It can be clearly seen that asymptotics are improved by erasure.

Shortcomings
============

You can't get warnings in libraries because usage analysis starts from
``Main.main``. This will be solved by the planned ``%default_usage``
pragma.

Usage warnings are quite bad and unhelpful at the moment. We should
include more information and at least translate argument numbers to
their names.

There is no decent documentation yet. This wiki page is the first one.

There is no generally accepted terminology. We switch between
"dotted", "unused", "erased", "irrelevant", "inaccessible", while each
has a slightly different meaning. We need more consistent and
understandable naming.

If the same type is used in both erased and non-erased context, it
will retain its fields to accommodate the least common denominator --
the non-erased context. This is particularly troublesome in the case
of the type of (dependent) pairs, where it actually means that no
erasure would be performed. We should probably locate disjoint uses of
data types and split them into "sub-types". There are three different
flavours of dependent types now: ``Sigma`` (nothing erased),
``Exists`` (first component erased), ``Subset`` (second component
erased).

Case-tree building does not avoid dotted values coming from
pattern-matched constructors (https://gist.github.com/ziman/10458331).
This is to be fixed soon. (Fixed.)

Higher-order function arguments and opaque functional variables are
considered to be using all their arguments. To work around this, you
can force erasure via the type system, using the ``Erased`` wrapper:
https://github.com/idris-lang/Idris-dev/blob/master/libs/base/Data/Erased.idr

Interface methods are considered to be using the union of all their
implementations. In other words, an argument of a method is unused
only if it is unused in every implementation of the method that occurs
in the program.

Planned features
================

- Fixes to the above shortcomings in general.

- Improvements to the case-tree elaborator so that it properly avoids
   dotted fields of data constructors. Done.

- Compiler pragma ``%default_usage used/unused`` and per-function
   overrides ``used`` and ``unused``, which allow the programmer to
   mark the return value of a function as used, even if the function
   is not used in ``main`` (which is the case when writing library
   code). These annotations will help library writers discover usage
   violations in their code before it is actually published and used
   in compiled programs.

Troubleshooting
===============

My program is slower
--------------------

The patch introducing erasure by usage analysis also disabled some
optimisations that were in place before; these are subsumed by the new
erasure. However, in some erasure-unaware programs, where erasure by
usage analysis does not exercise its full potential (but the old
optimisations would have worked), certain slowdown may be observed (up
to ~10% according to preliminary benchmarking), due to retention and
computation of information that should not be necessary at runtime.

A simple check whether this is the case is to compile with
``--warnreach``. If you see warnings, there is some unnecessary code
getting compiled into the binary.

The solution is to change the code so that there are no warnings.

Usage warnings are unhelpful
----------------------------

This is a known issue and we are working on it. For now, see the section
`How to read and resolve erasure
warnings <#how-to-read-and-resolve-erasure-warnings>`__.

There should be no warnings in this function
--------------------------------------------

A possible cause is non-totality of the function (more precisely,
non-coverage). If a function is non-covering, the program needs to
inspect all arguments in order to detect coverage failures at runtime.
Since the function inspects all its arguments, nothing can be erased
and this may transitively cause usage violations. The solution is to
make the function total or accept the fact that it will use its
arguments and remove some dots from the appropriate constructor fields
and function arguments. (Please note that this is not a shortcoming of
erasure and there is nothing we can do about it.)

Another possible cause is the currently imperfect case-tree
elaboration, which does not avoid dotted constructor fields (see
https://gist.github.com/ziman/10458331). You can either rephrase the
function or wait until this is fixed, hopefully soon. Fixed.

The compiler refuses to recognise this thing as erased
------------------------------------------------------

You can force anything to be erased by wrapping it in the ``Erased``
monad. While this program triggers usage warnings,

.. code-block:: idris

    f : (g : Nat -> Nat) -> .(x : Nat) -> Nat
    f g x = g x  -- WARNING: g uses x

the following program does not:

.. code-block:: idris

    f : (g : Erased Nat -> Nat) -> .(x : Nat) -> Nat
    f g x = g (Erase x)  -- OK

How to read and resolve erasure warnings
========================================

Example 1
---------

Consider the following program:

.. code-block:: idris

    vlen : Vect n a -> Nat
    vlen {n = n} xs = n

    sumLengths : List (Vect n a) -> Nat
    sumLengths       []  = 0
    sumLengths (v :: vs) = vlen v + sumLengths vs

    main : IO ()
    main = print . sumLengths $ [[0,1],[2,3]]

When you compile it using ``--warnreach``, there is one warning:

.. code-block:: idris

    Main.sumLengths: inaccessible arguments reachable:
      n (no more information available)

The warning does not contain much detail at this point so we can try
compiling with ``--dumpcases cases.txt`` and look up the compiled
definition in ``cases.txt``:

.. code-block:: idris

    Main.sumLengths {e0} {e1} {e2} =
      case {e2} of
      | Prelude.List.::({e6}) => LPlus (ATInt ITBig)({e0}, Main.sumLengths({e0}, ____, {e6}))
      | Prelude.List.Nil() => 0

The reason for the warning is that ``sumLengths`` calls ``vlen``, which
gets inlined. The second clause of ``sumLengths`` then accesses the
variable ``n``, compiled as ``{e0}``. Since ``n`` is a free implicit, it
is automatically considered dotted and this triggers the warning.

A solution would be either making the argument ``n`` a bound implicit
parameter to indicate that we wish to keep it at runtime,

.. code-block:: idris

    sumLengths : {n : Nat} -> List (Vect n a) -> Nat

or fixing ``vlen`` to not use the index:

.. code-block:: idris

    vlen : Vect n a -> Nat
    vlen [] = Z
    vlen (x :: xs) = S (vlen xs)

Which solution is appropriate depends on the usecase.

Example 2
---------

Consider the following program manipulating value-indexed binary
numbers.

.. code-block:: idris

    data Bin : Nat -> Type where
        N : Bin Z
        O : Bin n -> Bin (0 + n + n)
        I : Bin n -> Bin (1 + n + n)

    toN : (b : Bin n) -> Nat
    toN  N = Z
    toN (O {n} bs) = 0 + n + n
    toN (I {n} bs) = 1 + n + n

    main : IO ()
    main = print . toN $ I (I (O (O (I N))))

In the function ``toN``, we attempted to "cheat" and instead of
traversing the whole structure, we just projected the value index ``n``
out of constructors ``I`` and ``O``. However, this index is a free
implicit, therefore it is considered dotted.

Inspecting it then produces the following warnings when compiling with
``--warnreach``:

.. code-block:: idris

    Main.I: inaccessible arguments reachable:
      n from Main.toN arg# 1
    Main.O: inaccessible arguments reachable:
      n from Main.toN arg# 1

We can see that the argument ``n`` of both ``I`` and ``O`` is used in
the function ``toN``, argument 1.

At this stage of development, warnings only contain argument numbers,
not names; this will hopefully be fixed. When numbering arguments, we
go from 0, taking free implicits first, left-to-right; then the bound
arguments. The function ``toN`` has therefore in fact two arguments:
``n`` (argument 0) and ``b`` (argument 1). And indeed, as the warning
says, we project the dotted field from ``b``.

Again, one solution is to fix the function ``toN`` to calculate its
result honestly; the other one is to accept that we carry a ``Nat``
with every constructor of ``Bin`` and make it a bound implicit:

.. code-block:: idris

        O : {n : Nat} -> Bin n -> Bin (0 + n + n)
        I : {n : Nat} -> bin n -> Bin (1 + n + n)

References
==========

.. [BMM04] Edwin Brady, Conor McBride, James McKinna: `Inductive
           families need not store their indices
           <http://citeseerx.ist.psu.edu/viewdoc/summary;jsessionid=1F796FCF0F2C4C535FC70F62BE2FB821?doi=10.1.1.62.3849>`__
