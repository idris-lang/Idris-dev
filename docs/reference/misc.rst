**************
Miscellaneous
**************

Things we have yet to classify, or are two small to justify their own page.


The Unifier Log
===============

If you're having a hard time debugging why the unifier won't accept
something (often while debugging the compiler itself), try applying the
special operator ``%unifyLog`` to the expression in question. This will
cause the type checker to spit out all sorts of informative messages.


Namespaces and type-directed disambiguation
===========================================

Names can be defined in separate namespaces, and disambiguated by type.
An expression ``with NAME EXPR`` will privilege the namespace ``NAME``
in the expression ``EXPR``. For example:

::

    Idris> with List [[1,2],[3,4],[5,6]]
    [[1, 2], [3, 4], [5, 6]] : List (List Integer)

    Idris> with Vect [[1,2],[3,4],[5,6]]
    [[1, 2], [3, 4], [5, 6]] : Vect 3 (Vect 2 Integer)

    Idris> [[1,2],[3,4],[5,6]]
    Can't disambiguate name: Prelude.List.::, Prelude.Stream.::, Prelude.Vect.::


Alternatives
============

The syntax ``(| option1, option2, option3, ... |)`` type checks each
of the options in turn until one of them works. This is used, for
example, when translating integer literals.

::

    Idris> the Nat (| "foo", Z, (-3) |)
    0 : Nat


This can also be used to give simple automated proofs, for example: trying
some constructors of proofs.

::

    syntax Trivial = (| oh, refl |)


Totality checking assertions
============================

All definitions are checked for *coverage* (i.e. all well-typed
applications are handled) and either for *termination* (i.e. all
well-typed applications will eventually produce an answer) or, if
returning codata, for productivity (in practice, all recursive calls are
constructor guarded).

Obviously, termination checking is undecidable. In practice, the
termination checker looks for *size change* - every cycle of recursive
calls must have a decreasing argument, such as a recursive argument of a
strictly positive data type.

There are two built-in functions which can be used to give the totality
checker a hint:

-  ``assert_total x`` asserts that the expression ``x`` is terminating
   and covering, even if the totality checker cannot tell. This can be
   used for example if ``x`` uses a function which does not cover all
   inputs, but the caller knows that the specific input is covered.
-  ``assert_smaller p x`` asserts that the expression ``x`` is
   structurally smaller than the pattern ``p``.

For example, the following function is not checked as total:

::

    qsort : Ord a => List a -> List a
    qsort [] = []
    qsort (x :: xs) = qsort (filter (<= x) xs) ++ (x :: qsort (filter (>= x) xs)))

This is because the checker cannot tell that ``filter`` will always
produce a value smaller than the pattern ``x :: xs`` for the recursive
call to ``qsort``. We can assert that this will always be true as
follows:

::

    total
    qsort : Ord a => List a -> List a
    qsort [] = []
    qsort (x :: xs) = qsort (assert_smaller (x :: xs) (filter (<= x) xs)) ++
                      (x :: qsort (assert_smaller (x :: xs) (filter (>= x) xs))))


C heap
======

Idris has two heaps where objects can be allocated:

+--------------------------------------+---------------------------------------+
| FP heap                              | C heap                                |
+======================================+=======================================+
| Cheney-collected                     | Mark-and-sweep-collected              |
+--------------------------------------+---------------------------------------+
| Garbage collections touches only     | Garbage collection has to traverse    |
| live objects.                        | all registered items.                 |
+--------------------------------------+---------------------------------------+
| Ideal for FP-style rapid allocation  | Ideal for C-style allocation of a few |
| of lots of small short-lived pieces  | big buffers.                          |
| of memory, such as data constructors.|                                       |
+--------------------------------------+---------------------------------------+
| Finalizers are impossible to support | Items have finalizers that are called |
| reasonably.                          | on deallocation.                      |
+--------------------------------------+---------------------------------------+
| Data is copied all the time (when    | Copying does not happen.              |
| collecting garbage, modifying data,  |                                       |
| registering managed pointers, etc.)  |                                       |
+--------------------------------------+---------------------------------------+
| Contains objects of various types.   | Contains C heap items: ``(void *)``   |
|                                      | pointers with finalizers. A finalizer |
|                                      | is a routine that deallocates the     |
|                                      | resources associated with the item.   |
+--------------------------------------+---------------------------------------+
| Fixed set of object types.           | The data pointer may point            |
|                                      | to anything, as long as the finalizer |
|                                      | cleans up correctly.                  |
+--------------------------------------+---------------------------------------+
| Not suitable for C resources and     | Suitable for C resources and arbitrary|
| arbitrary pointers.                  | pointers.                             |
+--------------------------------------+---------------------------------------+
| Values form a compact memory block.  | Items are kept in a linked list.      |
+--------------------------------------+---------------------------------------+
| Any Idris value, most notably        | Items represented by the              |
| ``ManagedPtr``.                      | Idris type ``CData``.                 |
+--------------------------------------+---------------------------------------+
| Data of ``ManagedPtr`` allocated     | Data allocated in C, pointer copied   |
| in C, buffer then copied into the FP | into the C heap.                      |
| heap.                                |                                       |
+--------------------------------------+---------------------------------------+
| Allocation and reallocation not      | Allocated and reallocate freely in C, |
| possible from C code (without having | registering the allocated items       |
| a reference to the VM). Everything   | in the FFI.                           |
| is copied instead.                   |                                       |
+--------------------------------------+---------------------------------------+

The FP heap is the primary heap. It may contain values of type ``CData``,
which are references to items in the C heap. A C heap item contains
a ``(void *)`` pointer and the corresponding finalizer. Once a C heap item
is no longer referenced from the FP heap, it is marked as unused and
the next GC sweep will call its finalizer and deallocate it.

There is no Idris interface for ``CData`` other than its type and FFI.

Usage from C code
-----------------

* Although not enforced in code, ``CData`` is meant to be opaque
  and non-RTS code (such as libraries or C bindings) should
  access only its ``(void *)`` field called ``data``.

* Feel free to mutate both the pointer ``data`` (eg. after calling ``realloc``)
  and the memory it points to. However, keep in mind
  that this must not break Idris's referential transparency.

* **WARNING!** If you call ``cdata_allocate`` or ``cdata_manage``,
  the resulting ``CData`` object *must* be returned from your
  FFI function so that it is inserted in the C heap by the RTS.
  Otherwise the memory will be leaked.

.. code:: idris

    some_allocating_fun : Int -> IO CData
    some_allocating_fun i = foreign FFI_C "some_allocating_fun" (Int -> IO CData) i

    other_fun : CData -> Int -> IO Int
    other_fun cd i = foreign FFI_C "other_fun" (CData -> Int -> IO Int) cd i

.. code:: cpp

    #include "idris_rts.h"

    static void finalizer(void * data)
    {
        MyStruct * ptr = (MyStruct *) data;
        free_something(ptr->something);
        free(ptr);
    }

    CData some_allocating_fun(int arg)
    {
        void * data = (void *) malloc(...);
        // ...
        return cdata_manage(data, finalizer);
    }

    int other_fun(CData cd, int arg)
    {
        int result = foo(cd->data);
        return result;
    }

Preorder reasoning
==================

This syntax is defined in the module ``Syntax.PreorderReasoning`` in the
``base`` package. It provides a syntax for composing proofs of
reflexive-transitive relations, using overloadable functions called
``step`` and ``qed``. This module also defines ``step`` and ``qed``
functions allowing the syntax to be used for demonstrating equality.
Here is an example:

.. code:: idris

    import Syntax.PreorderReasoning
    multThree : (a, b, c : Nat) -> a * b * c = c * a * b
    multThree a b c =
      (a * b * c) ={ sym (multAssociative a b c) }=
      (a * (b * c)) ={ cong (multCommutative b c) }=
      (a * (c * b)) ={ multAssociative a c b }=
      (a * c * b) ={ cong {f = (* b)} (multCommutative a c) }=
      (c * a * b) QED

Note that the parentheses are required -- only a simple expression can
be on the left of ``={ }=`` or ``QED``. Also, when using preorder
reasoning syntax to prove things about equality, remember that you can
only relate the entire expression, not subexpressions. This might
occasionally require the use of ``cong``.

Finally, although equality is the most obvious application of preorder
reasoning, it can be used for any reflexive-transitive relation.
Something like ``step1 ={ just1 }= step2 ={ just2 }= end QED`` is
translated to ``(step step1 just1 (step step2 just2 (qed end)))``,
selecting the appropriate definitions of ``step`` and ``qed`` through
the normal disambiguation process. The standard library, for example,
also contains an implementation of preorder reasoning on isomorphisms.


Pattern matching on Implicit Arguments
======================================

Pattern matching is only allowed on implicit arguments when they are
referred by name, e.g.

.. code:: idris

    foo : {n : Nat} -> Nat
    foo {n = Z} = Z
    foo {n = S k} = k

or

.. code:: idris

    foo : {n : Nat} -> Nat
    foo {n = n} = n

The latter could be shortened to the following:

.. code:: idris

    foo : {n : Nat} -> Nat
    foo {n} = n

That is, ``{x}`` behaves like ``{x=x}``.


Existence of an implementation
==============================

In order to show that an implementation of some interface is defined for some
type, one could use the ``%implementation`` keyword:

.. code:: idris

    foo : Num Nat
    foo = %implementation

'match' application
===================

``ty <== name`` applies the function ``name`` in such a way that it has
the type ``ty``, by matching ``ty`` against the function's type. This
can be used in proofs, for example:

::

    plus_comm : (n : Nat) -> (m : Nat) -> (n + m = m + n)
    -- Base case
    (Z + m = m + Z) <== plus_comm =
        rewrite ((m + Z = m) <== plusZeroRightNeutral) ==>
                (Z + m = m) in refl

    -- Step case
    (S k + m = m + S k) <== plus_comm =
        rewrite ((k + m = m + k) <== plus_comm) in
        rewrite ((S (m + k) = m + S k) <== plusSuccRightSucc) in
            refl

Reflection
==========

Including ``%reflection`` functions and ``quoteGoal x by fn in t``,
which applies ``fn`` to the expected type of the current expression, and
puts the result in ``x`` which is in scope when elaborating ``t``.

Bash Completion
================

Use of ``optparse-applicative`` allows Idris to support Bash
completion.  You can obtain the completion script for Idris using the
following command::

   idris --bash-completion-script `which idris`


To enable completion for the lifetime of your current session, run the
following command::

   source <(idris --bash-completion-script `which idris`)


To enable completion permenatly you must either:

* Modify your bash init script with the above command.

* Add the completion script to the appropriate ``bash_completion.d/``
  folder on your machine.
