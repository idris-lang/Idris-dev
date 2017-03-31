.. _sect-misc:

**********
Miscellany
**********

In this section we discuss a variety of additional features:

+ auto, implicit, and default arguments;
+ literate programming;
+ interfacing with external libraries through the foreign function
+ interface;
+ type providers;
+ code generation; and
+ the universe hierarchy.

Auto implicit arguments
=======================

We have already seen implicit arguments, which allows arguments to be
omitted when they can be inferred by the type checker, e.g.

.. code-block:: idris

    index : {a:Type} -> {n:Nat} -> Fin n -> Vect n a -> a

In other situations, it may be possible to infer arguments not by type
checking but by searching the context for an appropriate value, or
constructing a proof. For example, the following definition of ``head``
which requires a proof that the list is non-empty:

.. code-block:: idris

    isCons : List a -> Bool
    isCons [] = False
    isCons (x :: xs) = True

    head : (xs : List a) -> (isCons xs = True) -> a
    head (x :: xs) _ = x

If the list is statically known to be non-empty, either because its
value is known or because a proof already exists in the context, the
proof can be constructed automatically. Auto implicit arguments allow
this to happen silently. We define ``head`` as follows:

.. code-block:: idris

    head : (xs : List a) -> {auto p : isCons xs = True} -> a
    head (x :: xs) = x

The ``auto`` annotation on the implicit argument means that Idris
will attempt to fill in the implicit argument by searching for a value
of the appropriate type. It will try the following, in order:

- Local variables, i.e. names bound in pattern matches or ``let`` bindings,
  with exactly the right type.
- The constructors of the required type. If they have arguments, it will
  search recursively up to a maximum depth of 100.
- Local variables with function types, searching recursively for the
  arguments.
- Any function with the appropriate return type which is marked with the
  ``%hint`` annotation.

In the case that a proof is not found, it can be provided explicitly as normal:

.. code-block:: idris

    head xs {p = ?headProof}

Implicit conversions
====================

Idris supports the creation of *implicit conversions*, which allow
automatic conversion of values from one type to another when required to
make a term type correct. This is intended to increase convenience and
reduce verbosity. A contrived but simple example is the following:

.. code-block:: idris

    implicit intString : Int -> String
    intString = show

    test : Int -> String
    test x = "Number " ++ x

In general, we cannot append an ``Int`` to a ``String``, but the
implicit conversion function ``intString`` can convert ``x`` to a
``String``, so the definition of ``test`` is type correct. An implicit
conversion is implemented just like any other function, but given the
``implicit`` modifier, and restricted to one explicit argument.

Only one implicit conversion will be applied at a time. That is,
implicit conversions cannot be chained. Implicit conversions of simple
types, as above, are however discouraged! More commonly, an implicit
conversion would be used to reduce verbosity in an embedded domain
specific language, or to hide details of a proof. Such examples are
beyond the scope of this tutorial.

Literate programming
====================

Like Haskell, Idris supports *literate* programming. If a file has
an extension of ``.lidr`` then it is assumed to be a literate file. In
literate programs, everything is assumed to be a comment unless the line
begins with a greater than sign ``>``, for example:

.. code-block:: idris

    > module literate

    This is a comment. The main program is below

    > main : IO ()
    > main = putStrLn "Hello literate world!\n"

An additional restriction is that there must be a blank line between a
program line (beginning with ``>``) and a comment line (beginning with
any other character).

Foreign function calls
======================

For practical programming, it is often necessary to be able to use
external libraries, particularly for interfacing with the operating
system, file system, networking, *et cetera*. Idris provides a
lightweight foreign function interface for achieving this, as part of
the prelude. For this, we assume a certain amount of knowledge of C and
the ``gcc`` compiler. First, we define a datatype which describes the
external types we can handle:

.. code-block:: idris

    data FTy = FInt | FFloat | FChar | FString | FPtr | FUnit

Each of these corresponds directly to a C type. Respectively: ``int``,
``double``, ``char``, ``char*``, ``void*`` and ``void``. There is also a
translation to a concrete Idris type, described by the following
function:

.. code-block:: idris

    interpFTy : FTy -> Type
    interpFTy FInt    = Int
    interpFTy FFloat  = Double
    interpFTy FChar   = Char
    interpFTy FString = String
    interpFTy FPtr    = Ptr
    interpFTy FUnit   = ()

A foreign function is described by a list of input types and a return
type, which can then be converted to an Idris type:

.. code-block:: idris

    ForeignTy : (xs:List FTy) -> (t:FTy) -> Type

A foreign function is assumed to be impure, so ``ForeignTy`` builds an
``IO`` type, for example:

.. code-block:: idris

    Idris> ForeignTy [FInt, FString] FString
    Int -> String -> IO String : Type

    Idris> ForeignTy [FInt, FString] FUnit
    Int -> String -> IO () : Type

We build a call to a foreign function by giving the name of the
function, a list of argument types and the return type. The built in
construct ``mkForeign`` converts this description to a function callable
by Idris:

.. code-block:: idris

    data Foreign : Type -> Type where
        FFun : String -> (xs:List FTy) -> (t:FTy) ->
               Foreign (ForeignTy xs t)

    mkForeign : Foreign x -> x

Note that the compiler expects ``mkForeign`` to be fully applied to
build a complete foreign function call. For example, the ``putStr``
function is implemented as follows, as a call to an external function
``putStr`` defined in the run-time system:

.. code-block:: idris

    putStr : String -> IO ()
    putStr x = mkForeign (FFun "putStr" [FString] FUnit) x

Include and linker directives
-----------------------------

Foreign function calls are translated directly to calls to C functions,
with appropriate conversion between the Idris representation of a
value and the C representation. Often this will require extra libraries
to be linked in, or extra header and object files. This is made possible
through the following directives:

-  ``%lib target x`` — include the ``libx`` library. If the target is
   ``C`` this is equivalent to passing the ``-lx`` option to ``gcc``. If
   the target is Java the library will be interpreted as a
   ``groupId:artifactId:packaging:version`` dependency coordinate for
   maven.

-  ``%include target x`` — use the header file or import ``x`` for the
   given back end target.

-  ``%link target x.o`` — link with the object file ``x.o`` when using
   the given back end target.

-  ``%dynamic x.so`` — dynamically link the interpreter with the shared
   object ``x.so``.

Testing foreign function calls
------------------------------

Normally, the Idris interpreter (used for typechecking and at the REPL)
will not perform IO actions. Additionally, as it neither generates C
code nor compiles to machine code, the ``%lib``, ``%include`` and
``%link`` directives have no effect. IO actions and FFI calls can be
tested using the special REPL command ``:x EXPR``, and C libraries can
be dynamically loaded in the interpreter by using the ``:dynamic``
command or the ``%dynamic`` directive. For example:

.. code-block:: idris

    Idris> :dynamic libm.so
    Idris> :x unsafePerformIO ((mkForeign (FFun "sin" [FFloat] FFloat)) 1.6)
    0.9995736030415051 : Double

Type Providers
==============

Idris type providers, inspired by F#’s type providers, are a means of
making our types be “about” something in the world outside of Idris. For
example, given a type that represents a database schema and a query that
is checked against it, a type provider could read the schema of a real
database during type checking.

Idris type providers use the ordinary execution semantics of Idris to
run an IO action and extract the result. This result is then saved as a
constant in the compiled code. It can be a type, in which case it is
used like any other type, or it can be a value, in which case it can be
used as any other value, including as an index in types.

Type providers are still an experimental extension. To enable the
extension, use the ``%language`` directive:

.. code-block:: idris

    %language TypeProviders

A provider ``p`` for some type ``t`` is simply an expression of type
``IO (Provider t)``. The ``%provide`` directive causes the type checker
to execute the action and bind the result to a name. This is perhaps
best illustrated with a simple example. The type provider ``fromFile``
reads a text file. If the file consists of the string ``Int``, then the
type ``Int`` will be provided. Otherwise, it will provide the type
``Nat``.

.. code-block:: idris

    strToType : String -> Type
    strToType "Int" = Int
    strToType _ = Nat

    fromFile : String -> IO (Provider Type)
    fromFile fname = do Right str <- readFile fname
		          | Left err => pure (Provide Void)
		        pure (Provide (strToType (trim str)))

We then use the ``%provide`` directive:

.. code-block:: idris

    %provide (T1 : Type) with fromFile "theType"

    foo : T1
    foo = 2

If the file named ``theType`` consists of the word ``Int``, then ``foo``
will be an ``Int``. Otherwise, it will be a ``Nat``. When Idris
encounters the directive, it first checks that the provider expression
``fromFile theType`` has type ``IO (Provider Type)``. Next, it executes
the provider. If the result is ``Provide t``, then ``T1`` is defined as
``t``. Otherwise, the result is an error.

Our datatype ``Provider t`` has the following definition:

.. code-block:: idris

    data Provider a = Error String
                    | Provide a

We have already seen the ``Provide`` constructor. The ``Error``
constructor allows type providers to return useful error messages. The
example in this section was purposefully simple. More complex type
provider implementations, including a statically-checked SQLite binding,
are available in an external collection [1]_.

C Target
========

The default target of Idris is C. Compiling via :

::

    $ idris hello.idr -o hello

is equivalent to :

::

    $ idris --codegen C hello.idr -o hello

When the command above is used, a temporary C source is generated, which
is then compiled into an executable named ``hello``.

In order to view the generated C code, compile via :

::

    $ idris hello.idr -S -o hello.c

To turn optimisations on, use the ``%flag C`` pragma within the code, as
is shown below :

.. code-block:: idris

    module Main
    %flag C "-O3"

    factorial : Int -> Int
    factorial 0 = 1
    factorial n = n * (factorial (n-1))

    main : IO ()
    main = do
         putStrLn $ show $ factorial 3

JavaScript Target
=================

Idris is capable of producing *JavaScript* code that can be run in a
browser as well as in the *NodeJS* environment or alike. One can use the
FFI to communicate with the *JavaScript* ecosystem.

Code Generation
---------------

Code generation is split into two separate targets. To generate code
that is tailored for running in the browser issue the following command:

::

    $ idris --codegen javascript hello.idr -o hello.js

The resulting file can be embedded into your HTML just like any other
*JavaScript* code.

Generating code for *NodeJS* is slightly different. Idris outputs a
*JavaScript* file that can be directly executed via ``node``.

::

    $ idris --codegen node hello.idr -o hello
    $ ./hello
    Hello world

Take into consideration that the *JavaScript* code generator is using
``console.log`` to write text to ``stdout``, this means that it will
automatically add a newline to the end of each string. This behaviour
does not show up in the *NodeJS* code generator.

Using the FFI
-------------

To write a useful application we need to communicate with the outside
world. Maybe we want to manipulate the DOM or send an Ajax request. For
this task we can use the FFI. Since most *JavaScript* APIs demand
callbacks we need to extend the FFI so we can pass functions as
arguments.

The *JavaScript* FFI works a little bit differently than the regular
FFI. It uses positional arguments to directly insert our arguments into
a piece of *JavaScript* code.

One could use the primitive addition of *JavaScript* like so:

.. code-block:: idris

    module Main

    primPlus : Int -> Int -> IO Int
    primPlus a b = mkForeign (FFun "%0 + %1" [FInt, FInt] FInt) a b

    main : IO ()
    main = do
      a <- primPlus 1 1
      b <- primPlus 1 2
      print (a, b)

Notice that the ``%n`` notation qualifies the position of the ``n``-th
argument given to our foreign function starting from 0. When you need a
percent sign rather than a position simply use ``%%`` instead.

Passing functions to a foreign function is very similar. Let’s assume
that we want to call the following function from the *JavaScript* world:

.. code-block:: idris

    function twice(f, x) {
      return f(f(x));
    }

We obviously need to pass a function ``f`` here (we can infer it from
the way we use ``f`` in ``twice``, it would be more obvious if
*JavaScript* had types).

The *JavaScript* FFI is able to understand functions as arguments when
you give it something of type ``FFunction``. The following example code
calls ``twice`` in *JavaScript* and returns the result to our Idris
program:

.. code-block:: idris

    module Main

    twice : (Int -> Int) -> Int -> IO Int
    twice f x = mkForeign (
      FFun "twice(%0,%1)" [FFunction FInt FInt, FInt] FInt
    ) f x

    main : IO ()
    main = do
      a <- twice (+1) 1
      print a

The program outputs ``3``, just like we expected.

Including external *JavaScript* files
-------------------------------------

Whenever one is working with *JavaScript* one might want to include
external libraries or just some functions that she or he wants to call
via FFI which are stored in external files. The *JavaScript* and
*NodeJS* code generators understand the ``%include`` directive. Keep in
mind that *JavaScript* and *NodeJS* are handled as different code
generators, therefore you will have to state which one you want to
target. This means that you can include different files for *JavaScript*
and *NodeJS* in the same Idris source file.

So whenever you want to add an external *JavaScript* file you can do
this like so:

For *NodeJS*:

.. code-block:: idris

      %include Node "path/to/external.js"

And for use in the browser:

.. code-block:: idris

      %include JavaScript "path/to/external.js"

The given files will be added to the top of the generated code.

Including *NodeJS* modules
--------------------------

The *NodeJS* code generator can also include modules with the ``%lib``
directive.

.. code-block:: idris

      %lib Node "fs"

This directive compiles into the following *JavaScript*

.. code-block:: javascript

      var fs = require("fs");

Shrinking down generated *JavaScript*
-------------------------------------

Idris can produce very big chunks of *JavaScript* code. However, the
generated code can be minified using the ``closure-compiler`` from
Google. Any other minifier is also suitable but ``closure-compiler``
offers advanced compilation that does some aggressive inlining and code
elimination. Idris can take full advantage of this compilation mode
and it’s highly recommended to use it when shipping a *JavaScript*
application written in Idris.

Cumulativity
============

Since values can appear in types and *vice versa*, it is natural that
types themselves have types. For example:

::

    *universe> :t Nat
    Nat : Type
    *universe> :t Vect
    Vect : Nat -> Type -> Type

But what about the type of ``Type``? If we ask Idris it reports

::

    *universe> :t Type
    Type : Type 1

If ``Type`` were its own type, it would lead to an inconsistency due to
`Girard’s paradox <http://www.cs.cmu.edu/afs/cs.cmu.edu/user/kw/www/scans/girard72thesis.pdf>`_ , so internally there is a
*hierarchy* of types (or *universes*):

.. code-block:: idris

    Type : Type 1 : Type 2 : Type 3 : ...

Universes are *cumulative*, that is, if ``x : Type n`` we can also have
that ``x : Type m``, as long as ``n < m``. The typechecker generates
such universe constraints and reports an error if any inconsistencies
are found. Ordinarily, a programmer does not need to worry about this,
but it does prevent (contrived) programs such as the following:

.. code-block:: idris

    myid : (a : Type) -> a -> a
    myid _ x = x

    idid :  (a : Type) -> a -> a
    idid = myid _ myid

The application of ``myid`` to itself leads to a cycle in the universe
hierarchy — ``myid``\ ’s first argument is a ``Type``, which cannot be
at a lower level than required if it is applied to itself.

.. [1]
   https://github.com/david-christiansen/idris-type-providers
