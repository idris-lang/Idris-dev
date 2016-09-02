.. _sect-repl:

**************
The Idris REPL
**************

Idris comes with a ``REPL``.

Evaluation
==========

Being a fully dependently typed language, Idris has two phases where it
evaluates things, compile-time and run-time. At compile-time it will only
evaluate things which it knows to be total (i.e. terminating and covering all
possible inputs) in order to keep type checking decidable. The compile-time
evaluator is part of the Idris kernel, and is implemented in Haskell using a
HOAS (higher order abstract syntax) style representation of values. Since
everything is known to have a normal form here, the evaluation strategy doesn't
actually matter because either way it will get the same answer, and in practice
it will do whatever the Haskell run-time system chooses to do.

The REPL, for convenience, uses the compile-time notion of evaluation. As well
as being easier to implement (because we have the evaluator available) this can
be very useful to show how terms evaluate in the type checker. So you can see
the difference between:

.. code-block:: idris

    Idris> \n, m => (S n) + m
    \n => \m => S (plus n m) : Nat -> Nat -> Nat

    Idris> \n, m => n + (S m)
    \n => \m => plus n (S m) : Nat -> Nat -> Nat

Customisation
=============

Idris supports initialisation scripts.

Initialisation scripts
~~~~~~~~~~~~~~~~~~~~~~

When the Idris REPL starts up, it will attempt to open the file
repl/init in Idris's application data directory. The application data
directory is the result of the Haskell function call
``getAppUserDataDirectory "idris"``, which on most Unix-like systems
will return $HOME/.idris and on various versions of Windows will return
paths such as ``C:/Documents And Settings/user/Application Data/appName``.

The file repl/init is a newline-separate list of REPL commands. Not all
commands are supported in initialisation scripts — only the subset that
will not interfere with the normal operation of the REPL. In particular,
setting colours, display options such as showing implicits, and log
levels are supported.

Example initialisation script
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
::

    :colour prompt white italic bold
    :colour implicit magenta italic



The ``REPL`` Commands
=====================

The current set of supported commands are:

+----------------+------------------------------+----------------------------------------------------------------------------------------------------------+
|Command         | Arguments                    | Purpose                                                                                                  |
+================+==============================+==========================================================================================================+
|<expr>          |                              | Evaluate an expression                                                                                   |
+----------------+------------------------------+----------------------------------------------------------------------------------------------------------+
|:t :type        | <expr>                       | Check the type of an expression                                                                          |
+----------------+------------------------------+----------------------------------------------------------------------------------------------------------+
|:core           | <expr>                       | View the core language representation of a term                                                          |
+----------------+------------------------------+----------------------------------------------------------------------------------------------------------+
|:miss :missing  | <name>                       | Show missing clauses                                                                                     |
+----------------+------------------------------+----------------------------------------------------------------------------------------------------------+
|:doc            | <name>                       | Show internal documentation                                                                              |
+----------------+------------------------------+----------------------------------------------------------------------------------------------------------+
|:mkdoc          | <namespace>                  | Generate IdrisDoc for namespace(s) and dependencies                                                      |
+----------------+------------------------------+----------------------------------------------------------------------------------------------------------+
|:apropos        | [<package list>] <name>      | Search names, types, and documentation                                                                   |
+----------------+------------------------------+----------------------------------------------------------------------------------------------------------+
|:s :search      | [<package list>] <expr>      | Search for values by type                                                                                |
+----------------+------------------------------+----------------------------------------------------------------------------------------------------------+
|:wc :whocalls   | <name>                       | List the callers of some name                                                                            |
+----------------+------------------------------+----------------------------------------------------------------------------------------------------------+
|:cw :callswho   | <name>                       | List the callees of some name                                                                            |
+----------------+------------------------------+----------------------------------------------------------------------------------------------------------+
|:browse         | <namespace>                  | List the contents of some namespace                                                                      |
+----------------+------------------------------+----------------------------------------------------------------------------------------------------------+
|:total          | <name>                       | Check the totality of a name                                                                             |
+----------------+------------------------------+----------------------------------------------------------------------------------------------------------+
|:r :reload      |                              | Reload current file                                                                                      |
+----------------+------------------------------+----------------------------------------------------------------------------------------------------------+
|:l :load        | <filename>                   | Load a new file                                                                                          |
+----------------+------------------------------+----------------------------------------------------------------------------------------------------------+
|:cd             | <filename>                   | Change working directory                                                                                 |
+----------------+------------------------------+----------------------------------------------------------------------------------------------------------+
|:module         | <module>                     | Import an extra module                                                                                   |
+----------------+------------------------------+----------------------------------------------------------------------------------------------------------+
|:e :edit        |                              | Edit current file using $EDITOR or $VISUAL                                                               |
+----------------+------------------------------+----------------------------------------------------------------------------------------------------------+
|:m :metavars    |                              | Show remaining proof obligations (holes)                                                                 |
+----------------+------------------------------+----------------------------------------------------------------------------------------------------------+
|:p :prove       | <hole>                       | Prove a hole                                                                                             |
+----------------+------------------------------+----------------------------------------------------------------------------------------------------------+
|:a :addproof    | <name>                       | Add proof to source file                                                                                 |
+----------------+------------------------------+----------------------------------------------------------------------------------------------------------+
|:rmproof        | <name>                       | Remove proof from proof stack                                                                            |
+----------------+------------------------------+----------------------------------------------------------------------------------------------------------+
|:showproof      | <name>                       | Show proof                                                                                               |
+----------------+------------------------------+----------------------------------------------------------------------------------------------------------+
|:proofs         |                              | Show available proofs                                                                                    |
+----------------+------------------------------+----------------------------------------------------------------------------------------------------------+
|:x              | <expr>                       | Execute IO actions resulting from an expression using the interpreter                                    |
+----------------+------------------------------+----------------------------------------------------------------------------------------------------------+
|:c :compile     | <filename>                   | Compile to an executable [codegen] <filename>                                                            |
+----------------+------------------------------+----------------------------------------------------------------------------------------------------------+
|:exec :execute  | [<expr>]                     | Compile to an executable and run                                                                         |
+----------------+------------------------------+----------------------------------------------------------------------------------------------------------+
|:dynamic        | <filename>                   | Dynamically load a C library (similar to %dynamic)                                                       |
+----------------+------------------------------+----------------------------------------------------------------------------------------------------------+
|:dynamic        |                              | List dynamically loaded C libraries                                                                      |
+----------------+------------------------------+----------------------------------------------------------------------------------------------------------+
|:? :h :help     |                              | Display this help text                                                                                   |
+----------------+------------------------------+----------------------------------------------------------------------------------------------------------+
|:set            | <option>                     | Set an option (errorcontext, showimplicits, originalerrors, autosolve, nobanner, warnreach, evaltypes,   |
|                |                              | desugarnats)                                                                                             |
+----------------+------------------------------+----------------------------------------------------------------------------------------------------------+
|:unset          | <option>                     | Unset an option                                                                                          |
+----------------+------------------------------+----------------------------------------------------------------------------------------------------------+
|:color :colour  | <option>                     | Turn REPL colours on or off; set a specific colour                                                       |
+----------------+------------------------------+----------------------------------------------------------------------------------------------------------+
|:consolewidth   | auto|infinite|<number>       | Set the width of the console                                                                             |
+----------------+------------------------------+----------------------------------------------------------------------------------------------------------+
|:printerdepth   | <number-or-blank>            | Set the maximum pretty-printing depth, or infinite if nothing specified                                  |
+----------------+------------------------------+----------------------------------------------------------------------------------------------------------+
|:q :quit        |                              | Exit the Idris system                                                                                    |
+----------------+------------------------------+----------------------------------------------------------------------------------------------------------+
|:w :warranty    |                              | Displays warranty information                                                                            |
+----------------+------------------------------+----------------------------------------------------------------------------------------------------------+
|:let            | (<top-level-declaration>)... | Evaluate a declaration, such as a function definition, instance implementation, or fixity declaration    |
+----------------+------------------------------+----------------------------------------------------------------------------------------------------------+
|:unlet :undefine|(<name>)...                   | Remove the listed repl definitions, or all repl definitions if no names given                            |
+----------------+------------------------------+----------------------------------------------------------------------------------------------------------+
|:printdef       | <name>                       | Show the definition of a function                                                                        |
+----------------+------------------------------+----------------------------------------------------------------------------------------------------------+
|:pp :pprint     | <option> <number> <name>     | Pretty prints an Idris function in either LaTeX or HTML and for a specified width.                       |
+----------------+------------------------------+----------------------------------------------------------------------------------------------------------+


Using the REPL
==============


Getting help
~~~~~~~~~~~~

The command ``:help`` (or ``:h`` or ``:?``) prints a short summary of
the available commands.

Quitting Idris
~~~~~~~~~~~~~~

If you would like to leave Idris, simply use ``:q`` or ``:quit``.

Evaluating expressions
~~~~~~~~~~~~~~~~~~~~~~

To evaluate an expression, simply type it. If Idris is unable to infer
the type, it can be helpful to use the operator ``the`` to manually
provide one, as Idris's syntax does not allow for direct type
annotations. Examples of ``the`` include:

::

    Idris> the Nat 4
    4 : Nat
    Idris> the Int 4
    4 : Int
    Idris> the (List Nat) [1,2]
    [1,2] : List Nat
    Idris> the (Vect _ Nat) [1,2]
    [1,2] : Vect 2 Nat

This may not work in cases where the expression still involves ambiguous
names. The name can be disambiguated by using the ``with`` keyword:

::

    Idris> sum [1,2,3]
    When elaborating an application of function Prelude.Foldable.sum:
            Can't disambiguate name: Prelude.List.::,
                                     Prelude.Stream.::,
                                     Prelude.Vect.::
    Idris> with List sum [1,2,3]
    6 : Integer

Adding let bindings
~~~~~~~~~~~~~~~~~~~

To add a let binding to the REPL, use ``:let``. It's likely you'll also
need to provide a type annotation. ``:let`` also works for other
declarations as well, such as ``data``.

::

    Idris> :let x : String; x = "hello"
    Idris> x
    "hello" : String
    Idris> :let y = 10
    Idris> y
    10 : Integer
    Idris> :let data Foo : Type where Bar : Foo
    Idris> Bar
    Bar : Foo

Getting type information
~~~~~~~~~~~~~~~~~~~~~~~~

To ask Idris for the type of some expression, use the ``:t`` command.
Additionally, if used with an overloaded name, Idris will provide all
overloadings and their types. To ask for the type of an infix operator,
surround it in parentheses.

::

    Idris> :t "foo"
    "foo" : String
    Idris> :t plus
    Prelude.Nat.plus : Nat -> Nat -> Nat
    Idris> :t (++)
    Builtins.++ : String -> String -> String
    Prelude.List.++ : (List a) -> (List a) -> List a
    Prelude.Vect.++ : (Vect m a) -> (Vect n a) -> Vect (m + n) a
    Idris> :t plus 4
    plus (Builtins.fromInteger 4) : Nat -> Nat

You can also ask for basic information about interfaces with ``:doc``:

::

    Idris> :doc Monad
    Interface Monad

    Parameters:
        m

    Methods:
        (>>=) : Monad m => m a -> (a -> m b) -> m b

            infixl 5

    Instances:
        Monad id
        Monad PrimIO
        Monad IO
        Monad Maybe

    ...

Other documentation is also available from ``:doc``:

::

    Idris> :doc (+)
    Prelude.Interfaces.(+) : Num ty => ty -> ty -> ty

    infixl 8

    The function is Total

::

    Idris> :doc Vect
    Data type Prelude.Vect.Vect : Nat -> Type -> Type

    Arguments:
            Nat
            Type

    Constructors:

    Prelude.Vect.Nil : (a : Type) -> Vect 0 a


    Prelude.Vect.:: : (a : Type) -> (n : Nat) -> a -> (Vect n a) -> Vect (S n) a

    infixr 7

    Arguments:
            a
            Vect n a

::

    Idris> :doc Monad
    Interface Monad

    Parameters:
        m

    Methods:
        (>>=) : Monad m => m a -> (a -> m b) -> m b
            Also called bind.
            infixl 5

            The function is Total
        join : Monad m => m (m a) -> m a
            Also called flatten or mu

            The function is Total
    Implementations:
        Monad (IO' ffi)
        Monad Stream
        Monad Provider
        Monad Elab
        Monad PrimIO
        Monad Maybe
        Monad (Either e)
        Monad List

Finding things
~~~~~~~~~~~~~~

The command ``:apropos`` searches names, types, and documentation for
some string, and prints the results. For example:

::

    Idris> :apropos eq
    eqPtr : Ptr -> Ptr -> IO Bool


    eqSucc : (left : Nat) -> (right : Nat) -> (left = right) -> S left = S right
    S preserves equality

    lemma_both_neq : ((x = x') -> _|_) -> ((y = y') -> _|_) -> ((x, y) = (x', y')) -> _|_


    lemma_fst_neq_snd_eq : ((x = x') -> _|_) -> (y = y') -> ((x, y) = (x', y)) -> _|_


    lemma_snd_neq : (x = x) -> ((y = y') -> _|_) -> ((x, y) = (x, y')) -> _|_


    lemma_x_eq_xs_neq : (x = y) -> ((xs = ys) -> _|_) -> (x :: xs = y :: ys) -> _|_


    lemma_x_neq_xs_eq : ((x = y) -> _|_) -> (xs = ys) -> (x :: xs = y :: ys) -> _|_


    lemma_x_neq_xs_neq : ((x = y) -> _|_) -> ((xs = ys) -> _|_) -> (x :: xs = y :: ys) -> _|_


    prim__eqB16 : Bits16 -> Bits16 -> Int

    prim__eqB16x8 : Bits16x8 -> Bits16x8 -> Bits16x8

    prim__eqB32 : Bits32 -> Bits32 -> Int

    prim__eqB32x4 : Bits32x4 -> Bits32x4 -> Bits32x4

    prim__eqB64 : Bits64 -> Bits64 -> Int

    prim__eqB64x2 : Bits64x2 -> Bits64x2 -> Bits64x2

    prim__eqB8 : Bits8 -> Bits8 -> Int

    prim__eqB8x16 : Bits8x16 -> Bits8x16 -> Bits8x16

    prim__eqBigInt : Integer -> Integer -> Int

    prim__eqChar : Char -> Char -> Int

    prim__eqFloat : Double -> Double -> Int

    prim__eqInt : Int -> Int -> Int

    prim__eqString : String -> String -> Int

    prim__syntactic_eq : (a : Type) -> (b : Type) -> (x : a) -> (y : b) -> Maybe (x = y)

    sequence : Traversable t => Applicative f => (t (f a)) -> f (t a)


    sequence_ : Foldable t => Applicative f => (t (f a)) -> f ()


    Eq : Type -> Type
    The Eq interface defines inequality and equality.

    GTE : Nat -> Nat -> Type
    Greater than or equal to

    LTE : Nat -> Nat -> Type
    Proofs that n is less than or equal to m

    gte : Nat -> Nat -> Bool
    Boolean test than one Nat is greater than or equal to another

    lte : Nat -> Nat -> Bool
    Boolean test than one Nat is less than or equal to another

    ord : Char -> Int
    Convert the number to its ASCII equivalent.

    replace : (x = y) -> (P x) -> P y
    Perform substitution in a term according to some equality.

    sym : (l = r) -> r = l
    Symmetry of propositional equality

    trans : (a = b) -> (b = c) -> a = c
    Transitivity of propositional equality

``:search`` does a type-based search, in the spirit of Hoogle. See `Type-directed search (:search) <https://github.com/idris-lang/Idris-dev/wiki/Type-directed-search-%28%3Asearch%29>`_ for more details. Here is an example:

::

    Idris> :search a -> b -> a
    = Prelude.Basics.const : a -> b -> a
    Constant function. Ignores its second argument.

    = assert_smaller : a -> b -> b
    Assert to the totality checker than y is always structurally
    smaller than x (which is typically a pattern argument)

    > malloc : Int -> a -> a


    > Prelude.pow : Num a => a -> Nat -> a


    > Prelude.Interfaces.(*) : Num a => a -> a -> a


    > Prelude.Interfaces.(+) : Num a => a -> a -> a
    ... (More results)

``:search`` can also look for dependent types:

::

    Idris> :search plus (S n) n = plus n (S n)
    < Prelude.Nat.plusSuccRightSucc : (left : Nat) ->
                                      (right : Nat) ->
                                      S (left + right) = left + S right

Loading and reloading Idris code
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

The command ``:l File.idr`` will load File.idr into the
currently-running REPL, and ``:r`` will reload the last file that was
loaded.

Totality
~~~~~~~~

All Idris definitions are checked for totality. The command
``:total <NAME>`` will display the result of that check. If a definition
is not total, this may be due to an incomplete pattern match. If that is
the case, ``:missing`` or ``:miss`` will display the missing cases.

Editing files
~~~~~~~~~~~~~

The command ``:e`` launches your default editor on the current module.
After control returns to Idris, the file is reloaded.

Invoking the compiler
~~~~~~~~~~~~~~~~~~~~~

The current module can be compiled to an executable using the command
``:c <FILENAME>`` or ``:compile <FILENAME>``. This command allows to
specify codegen, so for example JavaScript can be generated using
``:c javascript <FILENAME>``. The ``:exec`` command will compile the
program to a temporary file and run the resulting executable.

IO actions
~~~~~~~~~~

Unlike GHCI, the Idris REPL is not inside of an implicit IO monad. This
means that a special command must be used to execute IO actions.
``:x tm`` will execute the IO action ``tm`` in an Idris interpreter.

Dynamically loading C libraries
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Sometimes, an Idris program will depend on external libraries written in
C. In order to use these libraries from the Idris interpreter, they must
first be dynamically loaded. This is achieved through the
``%dynamic <LIB>`` directive in Idris source files or through the
``:dynamic <LIB>`` command at the REPL. The current set of dynamically
loaded libraries can be viewed by executing ``:dynamic`` with no
arguments. These libraries are available through the Idris FFI in `type
providers <#type-providers>`__ and ``:exec``.

Colours
=======

Idris terms are available in amazing colour! By default, the Idris REPL
uses colour to distinguish between data constructors, types or type
constructors, operators, bound variables, and implicit arguments. This
feature is available on all POSIX-like systems, and there are plans to
allow it to work on Windows as well.

If you do not like the default colours, they can be turned off using the
command

::

    :colour off

and, when boredom strikes, they can be re-enabled using the command

::

    :colour on

To modify a colour, use the command

::

    :colour <CATEGORY> <OPTIONS>

where ``<CATEGORY`` is one of ``keyword``, ``boundvar``, ``implicit``,
``function``, ``type``, ``data``, or ``prompt``, and is a
space-separated list drawn from the colours and the font options. The
available colours are ``default``, ``black``, ``yellow``, ``cyan``,
``red``, ``blue``, ``white``, ``green``, and ``magenta``. If more than
one colour is specified, the last one takes precedence. The available
options are ``dull`` and ``vivid``, ``bold`` and ``nobold``, ``italic``
and ``noitalic``, ``underline`` and ``nounderline``, forming pairs of
opposites. The colour ``default`` refers to your terminal's default
colour.

The colours used at startup can be changed using REPL initialisation
scripts.

Colour can be disabled at startup by the ``--nocolour`` command-line
option.
