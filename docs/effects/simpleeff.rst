.. _sect-simpleff:

**************
Simple Effects
**************

So far we have seen how to write programs with locally mutable state
using the ``STATE`` effect. To recap, we have the definitions below
in a module ``Effect.State``

.. code-block:: idris

    module Effect.State

    STATE : Type -> EFFECT

    get    :             Eff x  [STATE x]
    put    : x ->        Eff () [STATE x]
    putM   : y ->        Eff () [STATE x] [STATE y]
    update : (x -> x) -> Eff () [STATE x]

    Handler State m where { ... }

The last line, ``Handler State m where { ... }``, means that the ``STATE``
effect is usable in any computation context ``m``. That is, a program
which uses this effect and returns something of type ``a`` can be
evaluated to something of type ``m a`` using ``run``, for any
``m``. The lower case ``State`` is a data type describing the
operations which make up the ``STATE`` effect itself—we will go into
more detail about this in Section :ref:`sect-impleff`.

In this section, we will introduce some other supported effects,
allowing console I/O, exceptions, random number generation and
non-deterministic programming. For each effect we introduce, we will
begin with a summary of the effect, its supported operations, and the
contexts in which it may be used, like that above for ``STATE``, and
go on to present some simple examples. At the end, we will see some
examples of programs which combine multiple effects.

All of the effects in the library, including those described in this
section, are summarised in Appendix :ref:`sect-appendix`.

Console I/O
===========

Console I/O is supported with the ``STDIO``
effect, which allows reading and writing characters and strings to and
from standard input and standard output. Notice that there is a
constraint here on the computation context ``m``, because it only
makes sense to support console I/O operations in a context where we
can perform (or at the very least simulate) console I/O:

.. code-block:: idris

    module Effect.StdIO

    STDIO : EFFECT

    putChar  : Char ->   Eff () [STDIO]
    putStr   : String -> Eff () [STDIO]
    putStrLn : String -> Eff () [STDIO]

    getStr   :           Eff String [STDIO]
    getChar  :           Eff Char [STDIO]

    Handler StdIO IO where { ... }
    Handler StdIO (IOExcept a) where { ... }

Examples
--------

A program which reads the user’s name, then says hello, can be written
as follows:

.. code-block:: idris

    hello : Eff () [STDIO]
    hello = do putStr "Name? "
               x <- getStr
               putStrLn ("Hello " ++ trim x ++ "!")

We use ``trim`` here to remove the trailing newline from the
input. The resource associated with ``STDIO`` is simply the empty
tuple, which has a default value ``()``, so we can run this as
follows:

.. code-block:: idris

    main : IO ()
    main = run hello

In ``hello`` we could also use ``!``-notation instead of ``x <-
getStr``, since we only use the string that is read once:

.. code-block:: idris

    hello : Eff () [STDIO]
    hello = do putStr "Name? "
               putStrLn ("Hello " ++ trim !getStr ++ "!")

More interestingly, we can combine multiple effects in one
program. For example, we can loop, counting the number of people we’ve
said hello to:

.. code-block:: idris

    hello : Eff () [STATE Int, STDIO]
    hello = do putStr "Name? "
               putStrLn ("Hello " ++ trim !getStr ++ "!")
               update (+1)
               putStrLn ("I've said hello to: " ++ show !get ++ " people")
               hello

The list of effects given in ``hello`` means that the function can
call ``get`` and ``put`` on an integer state, and any functions which
read and write from the console. To run this, ``main`` does not need
to be changed.

Aside: Resource Types
---------------------

To find out the resource type of an effect, if necessary (for example
if we want to initialise a resource explicitly with ``runInit`` rather
than using a default value with ``run``) we can run the
``resourceType`` function at the REPL:

.. code-block:: idris

    *ConsoleIO> resourceType STDIO
    () : Type
    *ConsoleIO> resourceType (STATE Int)
    Int : Type

Exceptions
==========

The ``EXCEPTION``
effect is declared in module ``Effect.Exception``. This allows programs
to exit immediately with an error, or errors to be handled more
generally:

.. _eff-exception:
.. code-block:: idris

    module Effect.Exception

    EXCEPTION : Type -> EFFECT

    raise : a -> Eff b [EXCEPTION a]

    Handler (Exception a) Maybe where { ... }
    Handler (Exception a) List where { ... }
    Handler (Exception a) (Either a) where { ... }
    Handler (Exception a) (IOExcept a) where { ... }
    Show a => Handler (Exception a) IO where { ... }

Example
-------

Suppose we have a ``String`` which is expected to represent an integer
in the range ``0`` to ``n``. We can write a function ``parseNumber``
which returns an ``Int`` if parsing the string returns a number in the
appropriate range, or throws an exception otherwise. Exceptions are
parameterised by an error type:

.. code-block:: idris

    data Error = NotANumber | OutOfRange

    parseNumber : Int -> String -> Eff Int [EXCEPTION Error]
    parseNumber num str
       = if all isDigit (unpack str)
            then let x = cast str in
                 if (x >=0 && x <= num)
                    then pure x
                    else raise OutOfRange
            else raise NotANumber

Programs which support the ``EXCEPTION`` effect can be run in any
context which has some way of throwing errors, for example, we can run
``parseNumber`` in the ``Either Error`` context. It returns a value of
the form ``Right x`` if successful:

.. code-block:: idris

    *Exception> the (Either Error Int) $ run (parseNumber 42 "20")
    Right 20 : Either Error Int

Or ``Left e`` on failure, carrying the appropriate exception:

.. code-block:: idris

    *Exception> the (Either Error Int) $ run (parseNumber 42 "50")
    Left OutOfRange : Either Error Int

    *Exception> the (Either Error Int) $ run (parseNumber 42 "twenty")
    Left NotANumber : Either Error Int

In fact, we can do a little bit better with ``parseNumber``, and have
it return a *proof* that the integer is in the required range along
with the integer itself. One way to do this is define a type of
bounded integers, ``Bounded``:

.. code-block:: idris

    Bounded : Int -> Type
    Bounded x = (n : Int ** So (n >= 0 && n <= x))

Recall that ``So`` is parameterised by a ``Bool``, and only ``So
True`` is inhabited. We can use ``choose`` to construct such a value
from the result of a dynamic check:

.. code-block:: idris

    data So : Bool -> Type = Oh : So True

    choose : (b : Bool) -> Either (So b) (So (not b))

We then write ``parseNumber`` using ``choose`` rather than an
``if/then/else`` construct, passing the proof it returns on success as
the boundedness proof:

.. code-block:: idris

    parseNumber : (x : Int) -> String -> Eff (Bounded x) [EXCEPTION Error]
    parseNumber x str
       = if all isDigit (unpack str)
            then let num = cast str in
                 case choose (num >=0 && num <= x) of
                      Left p => pure (num ** p)
                      Right p => raise OutOfRange
            else raise NotANumber

Random Numbers
==============

Random number generation is also implemented by the library, in module
``Effect.Random``:

.. code-block:: idris

    module Effect.Random

    RND : EFFECT

    srand  : Integer ->            Eff () [RND]
    rndInt : Integer -> Integer -> Eff Integer [RND]
    rndFin : (k : Nat) ->          Eff (Fin (S k)) [RND]

    Handler Random m where { ... }

Random number generation is considered side-effecting because its
implementation generally relies on some external source of randomness.
The default implementation here relies on an integer *seed*, which can
be set with ``srand``. A specific seed will lead to a predictable,
repeatable sequence of random numbers. There are two functions which
produce a random number:

- ``rndInt``, which returns a random integer between the given lower
   and upper bounds.

- ``rndFin``, which returns a random element of a finite set
   (essentially a number with an upper bound given in its type).

Example
-------

We can use the ``RND`` effect to implement a simple guessing game. The
``guess`` function, given a target number, will repeatedly ask the
user for a guess, and state whether the guess is too high, too low, or
correct:

.. code-block:: idris

    guess : Int -> Eff () [STDIO]

For reference, the code for ``guess`` is given below:

.. _eff-game:
.. code-block:: idris

    guess : Int -> Eff () [STDIO]
    guess target
        = do putStr "Guess: "
             case run {m=Maybe} (parseNumber 100 (trim !getStr)) of
                  Nothing => do putStrLn "Invalid input"
                                guess target
                  Just (v ** _) =>
                             case compare v target of
                                 LT => do putStrLn "Too low"
                                          guess target
                                 EQ => putStrLn "You win!"
                                 GT => do putStrLn "Too high"
                                          guess target

Note that we use ``parseNumber`` as defined previously to read user input, but
we don’t need to list the ``EXCEPTION`` effect because we use a nested ``run``
to invoke ``parseNumber``, independently of the calling effectful program.

To invoke this, we pick a random number within the range 0–100,
having set up the random number generator with a seed, then run
``guess``:

.. code-block:: idris

    game : Eff () [RND, STDIO]
    game = do srand 123456789
              guess (fromInteger !(rndInt 0 100))

    main : IO ()
    main = run game

If no seed is given, it is set to the ``default`` value. For a less
predictable game, some better source of randomness would be required,
for example taking an initial seed from the system time. To see how to
do this, see the ``SYSTEM`` effect described in :ref:`sect-appendix`.


Non-determinism
===============

The listing below gives the definition of the non-determinism
effect, which allows a program to choose a value non-deterministically
from a list of possibilities in such a way that the entire computation
succeeds:

.. code-block:: idris

    import Effects
    import Effect.Select

    SELECT : EFFECT

    select : List a -> Eff a [SELECT]

    Handler Selection Maybe where { ... }
    Handler Selection List where { ... }

Example
-------

The ``SELECT`` effect can be used to solve constraint problems, such
as finding Pythagorean triples. The idea is to use ``select`` to give
a set of candidate values, then throw an exception for any combination
of values which does not satisfy the constraint:

.. code-block:: idris

    triple : Int -> Eff (Int, Int, Int) [SELECT, EXCEPTION String]
    triple max = do z <- select [1..max]
                    y <- select [1..z]
                    x <- select [1..y]
                    if (x * x + y * y == z * z)
                       then pure (x, y, z)
                       else raise "No triple"

This program chooses a value for ``z`` between ``1`` and ``max``, then
values for ``y`` and ``x``. In operation, after a ``select``, the
program executes the rest of the ``do``-block for every possible
assignment, effectively searching depth-first. If the list is empty
(or an exception is thrown) execution fails.

There are handlers defined for ``Maybe`` and ``List`` contexts, i.e.
contexts which can capture failure. Depending on the context ``m``,
``triple`` will either return the first triple it finds (if in
``Maybe`` context) or all triples in the range (if in ``List``
context). We can try this as follows:

.. code-block:: idris

    main : IO ()
    main = do print $ the (Maybe _) $ run (triple 100)
              print $ the (List _) $ run (triple 100)

``vadd`` revisited
==================

We now return to the ``vadd`` program from the introduction. Recall the
definition:

.. code-block:: idris

    vadd : Vect n Int -> Vect n Int -> Vect n Int
    vadd []        []        = []
    vadd (x :: xs) (y :: ys) = x + y :: vadd xs ys

Using , we can set up a program so that it reads input from a user,
checks that the input is valid (i.e both vectors contain integers, and
are the same length) and if so, pass it on to ``vadd``. First, we
write a wrapper for ``vadd`` which checks the lengths and throw an
exception if they are not equal. We can do this for input vectors of
length ``n`` and ``m`` by matching on the implicit arguments ``n`` and
``m`` and using ``decEq`` to produce a proof of their equality, if
they are equal:

.. code-block:: idris

    vadd_check : Vect n Int -> Vect m Int ->
                 Eff (Vect m Int) [EXCEPTION String]
    vadd_check {n} {m} xs ys with (decEq n m)
      vadd_check {n} {m=n} xs ys | (Yes Refl) = pure (vadd xs ys)
      vadd_check {n} {m}   xs ys | (No contra) = raise "Length mismatch"

To read a vector from the console, we implement a function of the
following type:

.. code-block:: idris

    read_vec : Eff (p ** Vect p Int) [STDIO]

This returns a dependent pair of a length, and a vector of that
length, because we cannot know in advance how many integers the user
is going to input. We can use ``-1`` to indicate the end of input:

.. code-block:: idris

    read_vec : Eff (p ** Vect p Int) [STDIO]
    read_vec = do putStr "Number (-1 when done): "
                  case run (parseNumber (trim !getStr)) of
                       Nothing => do putStrLn "Input error"
                                     read_vec
                       Just v => if (v /= -1)
                                    then do (_ ** xs) <- read_vec
                                            pure (_ ** v :: xs)
                                    else pure (_ ** [])
      where
        parseNumber : String -> Eff Int [EXCEPTION String]
        parseNumber str
          = if all (\x => isDigit x || x == '-') (unpack str)
               then pure (cast str)
               else raise "Not a number"

This uses a variation on ``parseNumber`` which does not require a
number to be within range.

Finally, we write a program which reads two vectors and prints the
result of pairwise addition of them, throwing an exception if the
inputs are of differing lengths:

.. code-block:: idris

    do_vadd : Eff () [STDIO, EXCEPTION String]
    do_vadd = do putStrLn "Vector 1"
                 (_ ** xs) <- read_vec
                 putStrLn "Vector 2"
                 (_ ** ys) <- read_vec
                 putStrLn (show !(vadd_check xs ys))

By having explicit lengths in the type, we can be sure that ``vadd``
is only being used where the lengths of inputs are guaranteed to be
equal.  This does not stop us reading vectors from user input, but it
does require that the lengths are checked and any discrepancy is dealt
with gracefully.


Example: An Expression Calculator
=================================

To show how these effects can fit together, let us consider an
evaluator for a simple expression language, with addition and integer
values.

.. code-block:: idris

    data Expr = Val Integer
              | Add Expr Expr

An evaluator for this language always returns an ``Integer``, and
there are no situations in which it can fail!

.. code-block:: idris

    eval : Expr -> Integer
    eval (Val x) = x
    eval (Add l r) = eval l + eval r

If we add variables, however, things get more interesting. The
evaluator will need to be able to access the values stored in
variables, and variables may be undefined.

.. code-block:: idris

    data Expr = Val Integer
              | Var String
              | Add Expr Expr

To start, we will change the type of ``eval`` so that it is effectful,
and supports an exception effect for throwing errors, and a state
containing a mapping from variable names (as ``String``) to their
values:

.. code-block:: idris

    Env : Type
    Env = List (String, Integer)

    eval : Expr -> Eff Integer [EXCEPTION String, STATE Env]
    eval (Val x)   = pure x
    eval (Add l r) = pure $ !(eval l) + !(eval r)

Note that we are using ``!``-notation to avoid having to bind
subexpressions in a ``do`` block. Next, we add a case for evaluating
``Var``:

.. code-block:: idris

    eval (Var x) = case lookup x !get of
                        Nothing => raise $ "No such variable " ++ x
                        Just val => pure val

This retrieves the state (with ``get``, supported by the ``STATE Env``
effect) and raises an exception if the variable is not in the
environment (with ``raise``, supported by the ``EXCEPTION String``
effect).

To run the evaluator on a particular expression in a particular
environment of names and their values, we can write a function which
sets the state then invokes ``eval``:

.. code-block:: idris

    runEval : List (String, Integer) -> Expr -> Maybe Integer
    runEval args expr = run (eval' expr)
      where eval' : Expr -> Eff Integer [EXCEPTION String, STATE Env]
            eval' e = do put args
                         eval e

We have picked ``Maybe`` as a computation context here; it needs to be
a context which is available for every effect supported by
``eval``. In particular, because we have exceptions, it needs to be a
context which supports exceptions. Alternatively, ``Either String`` or
``IO`` would be fine, for example.

What if we want to extend the evaluator further, with random number
generation? To achieve this, we add a new constructor to ``Expr``,
which gives a random number up to a maximum value:

.. code-block:: idris

    data Expr = Val Integer
              | Var String
              | Add Expr Expr
              | Random Integer

Then, we need to deal with the new case, making sure that we extend
the list of events to include ``RND``. It doesn't matter where ``RND``
appears in the list, as long as it is present:

.. code-block:: idris

    eval : Expr -> Eff Integer [EXCEPTION String, RND, STATE Env]

    eval (Random upper) = rndInt 0 upper

For test purposes, we might also want to print the random number which
has been generated:

.. code-block:: idris

    eval (Random upper) = do val <- rndInt 0 upper
                             putStrLn (show val)
                             pure val

If we try this without extending the effects list, we would see an
error something like the following:

::

    Expr.idr:28:6:When elaborating right hand side of eval:
    Can't solve goal
       SubList [STDIO]
               [(EXCEPTION String), RND, (STATE (List (String, Integer)))]

In other words, the ``STDIO`` effect is not available. We can correct
this simply by updating the type of ``eval`` to include ``STDIO``.

.. code-block:: idris

    eval : Expr -> Eff Integer [STDIO, EXCEPTION String, RND, STATE Env]

.. note:: Using ``STDIO`` will restrict the number of contexts in
          which ``eval`` can be ``run`` to those which support
          ``STDIO``, such as ``IO``. Once effect lists get longer, it
          can be a good idea instead to encapsulate sets of effects in
          a type synonym. This is achieved as follows, simply by
          defining a function which computes a type, since types are
          first class in Idris:

          .. code-block:: idris

              EvalEff : Type -> Type
              EvalEff t = Eff t [STDIO, EXCEPTION String, RND, STATE Env]

              eval : Expr -> EvalEff Integer
