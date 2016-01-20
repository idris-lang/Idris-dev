.. _sect-namespaces:

**********************
Modules and Namespaces
**********************

An Idris program consists of a collection of modules. Each module
includes an optional ``module`` declaration giving the name of the
module, a list of ``import`` statements giving the other modules which
are to be imported, and a collection of declarations and definitions of
types, interfaces and functions. For example, the listing below gives a
module which defines a binary tree type ``BTree`` (in a file
``Btree.idr``):

.. code-block:: idris

    module Btree

    data BTree a = Leaf
                 | Node (BTree a) a (BTree a)

    insert : Ord a => a -> BTree a -> BTree a
    insert x Leaf = Node Leaf x Leaf
    insert x (Node l v r) = if (x < v) then (Node (insert x l) v r)
                                       else (Node l v (insert x r))

    toList : BTree a -> List a
    toList Leaf = []
    toList (Node l v r) = Btree.toList l ++ (v :: Btree.toList r)

    toTree : Ord a => List a -> BTree a
    toTree [] = Leaf
    toTree (x :: xs) = insert x (toTree xs)


Then, this gives a main program (in a file
``bmain.idr``) which uses the ``Btree`` module to sort a list:

.. code-block:: idris

    module Main

    import Btree

    main : IO ()
    main = do let t = toTree [1,8,2,7,9,3]
              print (Btree.toList t)



The same names can be defined in multiple modules. This is possible
because in practice names are *qualified* with the name of the module.
The names defined in the ``Btree`` module are, in full:

+ ``Btree.BTree``
+ ``Btree.Leaf``
+ ``Btree.Node``
+ ``Btree.insert``
+ ``Btree.toList``
+ ``Btree.toTree``

If names are otherwise unambiguous, there is no need to give the fully
qualified name. Names can be disambiguated either by giving an explicit
qualification, or according to their type.

There is no formal link between the module name and its filename,
although it is generally advisable to use the same name for each. An
``import`` statement refers to a filename, using dots to separate
directories. For example, ``import foo.bar`` would import the file
``foo/bar.idr``, which would conventionally have the module declaration
``module foo.bar``. The only requirement for module names is that the
main module, with the ``main`` function, must be called
``Main``—although its filename need not be ``Main.idr``.

Export Modifiers
================

By default, all names defined in a module are exported for use by other
modules. However, it is good practice only to export a minimal interface
and keep internal details abstract. Idris allows functions, types,
and interfaces to be marked as: ``public``, ``abstract`` or ``private``:

-  ``public`` means that both the name and definition are exported. For
   functions, this means that the implementation is exported (which
   means, for example, it can be used in a dependent type). For data
   types, this means that the type name and the constructors are
   exported. For interfaces, this means that the interface name and method
   names are exported.

-  ``abstract`` means that only the name is exported. For functions,
   this means that the implementation is not exported. For data types,
   this means that the type name is exported but not the constructors.
   For interfaces, this means that the interface name is exported but not the
   method names.

-  ``private`` means that neither the name nor the definition is
   exported.

.. note::
    If any definition is given an export modifier, then all names with no modifier are assumed to be ``private``.

For our ``Btree`` module, it makes sense for the tree data type and the
functions to be exported as ``abstract``, as we see below:

.. code-block:: idris

    module Btree

    abstract data BTree a = Leaf
                          | Node (BTree a) a (BTree a)

    abstract
    insert : Ord a => a -> BTree a -> BTree a
    insert x Leaf = Node Leaf x Leaf
    insert x (Node l v r) = if (x < v) then (Node (insert x l) v r)
                                       else (Node l v (insert x r))

    abstract
    toList : BTree a -> List a
    toList Leaf = []
    toList (Node l v r) = Btree.toList l ++ (v :: Btree.toList r)

    abstract
    toTree : Ord a => List a -> BTree a
    toTree [] = Leaf
    toTree (x :: xs) = insert x (toTree xs)

Finally, the default export mode can be changed with the ``%access``
directive, for example:

.. code-block:: idris

    module Btree

    %access abstract

    data BTree a = Leaf
                          | Node (BTree a) a (BTree a)

    insert : Ord a => a -> BTree a -> BTree a
    insert x Leaf = Node Leaf x Leaf
    insert x (Node l v r) = if (x < v) then (Node (insert x l) v r)
                                       else (Node l v (insert x r))

    toList : BTree a -> List a
    toList Leaf = []
    toList (Node l v r) = Btree.toList l ++ (v :: Btree.toList r)

    toTree : Ord a => List a -> BTree a
    toTree [] = Leaf
    toTree (x :: xs) = insert x (toTree xs)

In this case, any function with no access modifier will be exported as
``abstract``, rather than left ``private``.

Additionally, a module can re-export a module it has imported, by using
the ``public`` modifier on an ``import``. For example:

.. code-block:: idris

    module A

    import B
    import public C

    public a : AType a = ...

The module ``A`` will export the name ``a``, as well as any public or
abstract names in module ``C``, but will not re-export anything from
module ``B``.

Explicit Namespaces
===================

Defining a module also defines a namespace implicitly. However,
namespaces can also be given *explicitly*. This is most useful if you
wish to overload names within the same module:

.. code-block:: idris

    module Foo

    namespace x
      test : Int -> Int
      test x = x * 2

    namespace y
      test : String -> String
      test x = x ++ x

This (admittedly contrived) module defines two functions with fully
qualified names ``foo.x.test`` and ``foo.y.test``, which can be
disambiguated by their types:

::

    *foo> test 3
    6 : Int
    *foo> test "foo"
    "foofoo" : String

Parameterised blocks
====================

Groups of functions can be parameterised over a number of arguments
using a ``parameters`` declaration, for example:

.. code-block:: idris

    parameters (x : Nat, y : Nat)
      addAll : Nat -> Nat
      addAll z = x + y + z

The effect of a ``parameters`` block is to add the declared parameters
to every function, type and data constructor within the
block. Specifically, adding the parameters to the front of the
argument list. Outside the block, the parameters must be given
explicitly. The ``addAll`` function, when called from the REPL, will
thus have the following type signature.

::

    *params> :t addAll
    addAll : Nat -> Nat -> Nat -> Nat

and the following definition.

.. code-block:: idris

    addAll : (x : Nat) -> (y : Nat) -> (z : Nat) -> Nat
    addAll x y z = x + y + z

Parameters blocks can be nested, and can also include data declarations,
in which case the parameters are added explicitly to all type and data
constructors. They may also be dependent types with implicit arguments:

.. code-block:: idris

    parameters (y : Nat, xs : Vect x a)
      data Vects : Type -> Type where
        MkVects : Vect y a -> Vects a

      append : Vects a -> Vect (x + y) a
      append (MkVects ys) = xs ++ ys

To use ``Vects`` or ``append`` outside the block, we must also give the
``xs`` and ``y`` arguments. Here, we can use placeholders for the values
which can be inferred by the type checker:

::

    *params> show (append _ _ (MkVects _ [1,2,3] [4,5,6]))
    "[1, 2, 3, 4, 5, 6]" : String
