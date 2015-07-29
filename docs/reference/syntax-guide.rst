**************
Syntax Guide
**************

Examples are mostly adapted from the Idris tutorial.

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
variables that denote a type must beging with a capital letter. Example:

.. code:: idris

    MyIntType : Type
    MyIntType = Int

a more interesting example:

.. code:: idris

    MyListType : Type
    MyListType = List Int

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
GADT style syntax. This syntax defines a data type that is parameterized
by some values (in the ``Vect`` exampe, a value of type ``Nat`` and a
value of type ``Type``).

.. code:: idris

    data Vect : Nat -> Type -> Type where
      Nil  : Vect Z a
      (::) : (x : a) -> (xs : Vect n a) -> Vect (S n) a

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
expression which depends on the input parameter ``n``. ### Anonymous
Arguments in anonymous functions are separated by comma.

::

    (\x => <expr>)
    (\x, y => <expr>)

Modifiers
~~~~~~~~~

Visibility
^^^^^^^^^^

::

    public
    abstract
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
