**************
Syntax Guide
**************

Examples are mostly adapted from the Idris tutorial.

Source File Structure
---------------------

Source files consist of:

1. An optional :ref:`syntax-module-headers`.
2. Zero or more :ref:`syntax-imports`.
3. Zero or more declarations, e.g. :ref:`syntax-variables`,
   :ref:`syntax-data-types`, etc.

For example:

.. code:: idris

    module MyModule   -- module header

    import Data.Vect  -- an import

    %default total    -- a directive

    foo : Nat         -- a declaration
    foo = 5

.. _syntax-module-headers:

Module Header
~~~~~~~~~~~~~

A file can start with a module header, introduced by the ``module`` keyword:

.. code-block:: idris

  module Semantics

Module names can be hierarchical, with parts separated by ``.``:

.. code-block:: idris

  module Semantics.Transform

Each file can define only a single module, which includes everything defined in
that file.

Like with declarations, a :ref:`docstring <syntax-comments>` can be used to
provide documentation for a module:

.. code-block:: idris

  ||| Implementation of predicate transformer semantics.
  module Semantics.Transform

.. _syntax-imports:

Imports
~~~~~~~

An ``import`` makes the names in another module available for use by the current
module:

.. code-block:: idris

    import Data.Vect

All the declarations in an imported module are available for use in the file.
In a case where a name is ambiguous --- e.g. because it is imported from
multiple modules, or appears in multiple visible namespaces --- the ambiguity can be resolved using :ref:`syntax-qualified-names`.  (Often, the compiler can
resolve the ambiguity for you, using the types involved.)

Imported modules can be given aliases to make qualified names more compact:

.. code-block:: idris

    import Data.Vect as V

Note that names made visible by import are not, by default, re-exported to
users of the module being written.  This can be done using ``import public``:

.. code-block:: idris

    import public Data.Vect

.. _syntax-variables:

Variables
---------

A variable is always defined by defining its type on one line, and its
value on the next line, using the syntax

::

    <id> : <type>
    <id> = <value>

Examples

.. code:: idris

    x : Int
    x = 100
    hello : String
    hello = "hello"

Types
-----

In Idris, types are first class values. So a type declaration is the
same as just declaration of a variable whose type is ``Type``. In Idris,
variables that denote a type need not be capitalised. Example:

.. code:: idris

    MyIntType : Type
    MyIntType = Int

a more interesting example:

.. code:: idris

    MyListType : Type
    MyListType = List Int

While capitalising types is not required, the rules for generating implicit
arguments mean it is often a good idea.

.. _syntax-data-types:

Data types
~~~~~~~~~~

Idris provides two kinds of syntax for defining data types. The first,
Haskell style syntax, defines a regular algebraic data type. For example

.. code:: idris

    data Either a b = Left a | Right b

or

.. code:: idris

    data List a = Nil | (::) a (List a)

The second, more general kind of data type, is defined using Agda or
GADT style syntax. This syntax defines a data type that is parameterised
by some values (in the ``Vect`` example, a value of type ``Nat`` and a
value of type ``Type``).

.. code:: idris

    data Vect : Nat -> Type -> Type where
      Nil  : Vect Z a
      (::) : (x : a) -> (xs : Vect n a) -> Vect (S n) a

The signature of type constructors may use dependent types

.. code:: idris

    data DPair : (a : Type) -> (a -> Type) -> Type where
      MkDPair : {P : a -> Type} -> (x : a) -> (pf : P x) -> DPair a P

Records
~~~~~~~

There is a special syntax for data types with one constructors and
multiple fields.

.. code:: idris

    record A a where
      constructor MkA
      foo, bar : a
      baz : Nat

This defines a constructor as well as getter and setter function for
each field.

.. code:: idris

    MkA : a -> a -> Nat -> A a
    foo : A a -> a
    set_foo : a -> A a -> A a

The types of record fields may depend on the value of other fields

.. code:: idris

    record Collection a where
      constructor MkCollection
      size : Nat
      items : Vect size a

Setter functions are only provided for fields that do not use dependant
types. In the example above neither ``set_size`` nor ``set_items`` are
defined.


Co-data
~~~~~~~

Inifinite data structures can be introduced with the ``codata``
keyword.

.. code:: idris

  codata Stream : Type -> Type where
    (::) a -> Stream a -> Stream a

This is syntactic sugar for the following, which is usually preferred:

.. code:: idris

  data Stream : Type -> Type where
    (::) a -> Inf (Stream a) -> Stream a

Every occurence of the the defined type in a constructor argument will be
wrapped in the ``Inf`` type constructor. This has the effect of delaying the
evaluation of the second argument when the data constructor is applied.
An ``Inf`` argument is constructed using ``Delay`` (which Idris will insert
implicitly) adn evaluated using ``Force`` (again inserted implicitly).

Furthermore, recursive calls under a ``Delay`` must be guarded by a constructor
to pass the totality checker.

Operators
---------

Arithmetic
~~~~~~~~~~

::

    x + y
    x - y
    x * y
    x / y
    (x * y) + (a / b)

Equality and Relational
~~~~~~~~~~~~~~~~~~~~~~~

::

    x == y
    x /= y
    x >= y
    x > y
    x <= y
    x < y

Conditional
~~~~~~~~~~~

::

    x && y
    x || y
    not x

Conditionals
------------

If Then Else
~~~~~~~~~~~~

::

    if <test> then <true> else <false>

Case Expressions
~~~~~~~~~~~~~~~~

::

    case <test> of
        <case 1>  => <expr>
        <case 2>  => <expr>
        ...
        otherwise => <expr>

Functions
---------

Named
~~~~~

Named functions are defined in the same way as variables, with the type
followed by the definition.

::

    <id> : <argument type> -> <return type>
    <id> arg = <expr>

Example

.. code:: idris

    plusOne : Int -> Int
    plusOne x = x + 1

Functions can also have multiple inputs, for example

.. code:: idris

    makeHello : String -> String -> String
    makeHello first last = "hello, my name is " ++ first ++ " " ++ last

Functions can also have named arguments. This is required if you want to
annotate parameters in a docstring. The following shows the same
``makeHello`` function as above, but with named parameters which are
also annotated in the docstring

.. code:: idris

    ||| Makes a string introducing a person
    ||| @first The person's first name
    ||| @last The person's last name
    makeHello : (first : String) -> (last : String) -> String
    makeHello first last = "hello, my name is " ++ first ++ " " ++ last

Like Haskell, Idris functions can be defined by pattern matching. For
example

.. code:: idris

    sum : List Int -> Int
    sum []        = 0
    sum (x :: xs) = x + (sum xs)

Similarly case analysis looks like

.. code:: idris

    answerString : Bool -> String
    answerString False = "Wrong answer"
    answerString True = "Correct answer"

Dependent Functions
~~~~~~~~~~~~~~~~~~~

Dependent functions are functions where the type of the return value
depends on the input value. In order to define a dependent function,
named parameters must be used, since the parameter will appear in the
return type. For example, consider

.. code:: idris

    zeros : (n : Nat) -> Vect n Int
    zeros Z     = []
    zeros (S k) = 0 :: (zeros k)

In this example, the return type is ``Vect n Int`` which is an
expression which depends on the input parameter ``n``.

Anonymous
~~~~~~~~~

Arguments in anonymous functions are separated by comma.

::

    (\x => <expr>)
    (\x, y => <expr>)

Modifiers
~~~~~~~~~

Visibility
^^^^^^^^^^

::

    public export
    export
    private

Totality
^^^^^^^^

::

    total
    implicit
    partial
    covering

Options
^^^^^^^

::

    %export
    %hint
    %no_implicit
    %error_handler
    %error_reverse
    %assert_total
    %reflection
    %specialise [<name list>]

Misc
----

.. _syntax-qualified-names:

Qualified Names
~~~~~~~~~~~~~~~

If multiple declarations with the same name are visible, using the name can
result in an ambiguous situation.  The compiler will attempt to resolve the
ambiguity using the types involved.  If it's unable --- for example, because
the declarations with the same name also have the same type signatures --- the
situation can be cleared up using a *qualified name*.

A qualified name has the symbol's namespace prefixed, separated by a ``.``:

.. code-block:: idris

  Data.Vect.length

This would specifically reference a ``length`` declaration from ``Data.Vect``.

Qualified names can be written using two different shorthands:

1. Names in modules that are :ref:`imported <syntax-imports>` using an alias
   can be qualified by the alias.

2. The name can be qualified by the *shortest unique suffix* of the
   namespace in question.  For example, the ``length`` case above can likely
   be shortened to ``Vect.length``.

.. _syntax-comments:

Comments
~~~~~~~~

::

    -- Single Line
    {- Multiline -}
    ||| Docstring (goes before definition)

Multi line String literals
~~~~~~~~~~~~~~~~~~~~~~~~~~

::

    foo = """
    this is a
    string literal"""

.. _syntax-directives:

Directives
----------

::

    %lib <path>
    %link <path>
    %flag <path>
    %include <path>
    %hide <function>
    %freeze <name>
    %access <accessibility>
    %default <totality>
    %logging <level 0--11>
    %dynamic <list of libs>
    %name <list of names>
    %error_handlers <list of names>
    %language <extension>
