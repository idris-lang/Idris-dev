********************
Visibility Modifiers
********************

Since Idris ``v0.10.2`` new visibility modifiers were introduced.
This guide presents an extended series of examples to explain the use
of these new modifiers in action.

.. important:: To provide better intuition over the visibility
               modifiers it is important to remember that when
               importing a module what you are effectivly doing is
               including the API of the module in question for use.


Building a Module's API
=======================

Within Idris, a module's visibility is set to ``private``, in which no
information concerning the module is exposed. Take for example the following tree implementation in a module called ``MyTree``.

.. code-block:: idris

    module MyTree

    data T : Type -> Type where
      Leaf : T a
      Node : Show a => a -> T a -> T a -> T a

    treeShow : Show a => T a -> String
    treeShow (Leaf)       = "Leaf"
    treeShow (Node v l r) = unwords ["Node", show v, treeShow l, treeShow r]

    implementation (Show a) => Show T a where
        show t = treeShow t

    namespace Main
      example : T String
      example = Node "Foo" Leaf Leaf

      main : IO ()
      main = printLn $ Main.example


If we were to include the module in another program using an
``import`` statement nothing about this module will be accessible: the
API is currently blank. To expose (i.e. build) the API, we need to
begin exposing the contents of our module. We can do this at a module
level using the ``%access`` directive, and setting the module's
default visibility to be ``export``.
The first couple of lines for ``MyTree`` should now look like:

.. code-block:: idris

    module MyTree

    %access export


Remember, ``export`` allows us to expose top-level type declarations.
The exposed API for ``MyTree`` will now look like:

+ ``T : Type -> Type``
+ ``treeShow : Show a => T a -> String``
+ ``implementation (Show a) => Show (T a)``
+ ``Main.example : T String``
+ ``main  : IO ()``


Lets now spin out the ``Main`` namespace into a separate
module. Resulting in two files ``MyTree.idr`` and ``Main.idr``.  This
will remove the last two entries on the API for ``MyTree``.

However, do you notice that we are exporting the implementation of
``Show`` for ``T`` twice. The first is the actual implementation, and
the second when exporting the ``Show`` instance. To fix this we can
use the ``private`` modifier on ``treeShow`` to restrict the addition
of the function outside of the module itself.

A secondary problem is that the data structure instance ``example``,
now residing in ``Main.idr``, will no longer work. Idris will complain
that it doesn't know about the constructors ``Leaf`` and ``Node``. One fix is to add both constructors to the API by completely exposing the ``T`` data structure by setting its visibility to ``public export``.

.. code-block:: idris

    public export
    data T : Type -> Type where
      Leaf : T a
      Node : Show a => a -> T a -> T a -> T a


While this is possible, it is not always a good idea to expose your
data structure's implementation, nor should the user of your module
need to see this implementation all the time. To facilitate tree construction factories can be provided. A suitable set are:

.. code-block:: idris

    mkLeaf : T a
    mkLeaf = Leaf

    namespace WithChild
      mkNode : Show a => a -> T a -> T a -> T a
      mkNode = Node

    namespace NoChild
      mkNode : Show a => a -> T a
      mkNode v = Node v Leaf Leaf


The first function ``mkLeaf`` facilitates the construction of leaf nodes.
The second set of functions are for constructing nodes that have children, and nodes that do not have children. Idris' ability to perform type-directed namespace disambiguation will distinguish between the functions during use. Regardless with these new functions the exposed API for ``MyTree`` will now consist of:

+ ``T : Type -> Type``
+ ``implementation (Show a) => Show (T a)``
+ ``mkLeaf : T a``
+ ``WithChild.mkNode``
+ ``NoChild.mkNode : Show a => a -> T a``


With this API the data structure instance ``example`` can be reformulated as:

.. code-block:: idris

    example :: T String
    example = mkNode "Foo"


With this simple example, we can use Idris' visibility modifiers to
build a module's API, and expose the bits that are needed. Next we
will look at how to build a more complicated API for a module.
