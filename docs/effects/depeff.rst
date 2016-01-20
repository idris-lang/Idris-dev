.. _sect-depeff:

*****************
Dependent Effects
*****************

In the programs we have seen so far, the available effects have remained
constant. Sometimes, however, an operation can *change* the available
effects. The simplest example occurs when we have a state with a
dependent type—adding an element to a vector also changes its type, for
example, since its length is explicit in the type. In this section, we
will see how the library supports this. Firstly, we will see how states
with dependent types can be implemented. Secondly, we will see how the
effects can depend on the *result* of an effectful operation. Finally,
we will see how this can be used to implement a type-safe and
resource-safe protocol for file management.

Dependent States
================

Suppose we have a function which reads input from the console, converts
it to an integer, and adds it to a list which is stored in a ``STATE``.
It might look something like the following:

.. code-block:: idris

    readInt : Eff () [STATE (List Int), STDIO] 
    readInt = do let x = trim !getStr
                 put (cast x :: !get)

But what if, instead of a list of integers, we would like to store a
``Vect``, maintaining the length in the type?

.. code-block:: idris

    readInt : Eff () [STATE (Vect n Int), STDIO]
    readInt = do let x = trim !getStr
                 put (cast x :: !get)

This will not type check! Although the vector has length ``n`` on entry
to ``readInt``, it has length ``S n`` on exit. The library allows us to
express this as follows:

.. code-block:: idris

    readInt : Eff ()[STATE (Vect n Int), STDIO] 
                    [STATE (Vect (S n) Int), STDIO]
    readInt = do let x = trim !getStr
                 putM (cast x :: !get)

The type ``Eff a xs xs'`` means that the operation
begins with effects ``xs`` available, and ends with effects ``xs’``
available. We have used ``putM`` to update the state, where the ``M``
suffix indicates that the *type* is being updated as well as the value.
It has the following type:

.. code-block:: idris

    putM : y -> Eff () [STATE x] [STATE y]

Result-dependent Effects
========================

Often, whether a state is updated could depend on the success or
otherwise of an operation. In our ``readInt`` example, we might wish to
update the vector only if the input is a valid integer (i.e. all
digits). As a first attempt, we could try the following, returning a
``Bool`` which indicates success:

.. code-block:: idris

    readInt : Eff Bool [STATE (Vect n Int), STDIO]
                       [STATE (Vect (S n) Int), STDIO]
    readInt = do let x = trim !getStr
                 case all isDigit (unpack x) of
                      False => pure False
                      True => do putM (cast x :: !get)
                                 pure True

Unfortunately, this will not type check because the vector does not get
extended in both branches of the ``case``!

::

    MutState.idr:18:19:When elaborating right hand side of Main.case
    block in readInt:
    Unifying n and S n would lead to infinite value

Clearly, the size of the resulting vector depends on whether or not the
value read from the user was valid. We can express this in the type:

.. code-block:: idris

    readInt : Eff Bool [STATE (Vect n Int), STDIO]
                (\ok => if ok then [STATE (Vect (S n) Int), STDIO]
                              else [STATE (Vect n Int), STDIO])
    readInt = do let x = trim !getStr
                 case all isDigit (unpack x) of
                      False => pureM False
                      True => do putM (cast x :: !get)
                                 pureM True

Using ``pureM`` rather than ``pure`` allows the output effects to be
calculated from the value given. Its type is:

.. code-block:: idris

    pureM : (val : a) -> EffM m a (xs val) xs

When using ``readInt``, we will have to check its return
value in order to know what the new set of effects is. For example, to
read a set number of values into a vector, we could write the following:

.. code-block:: idris

    readN : (n : Nat) ->
            Eff () [STATE (Vect m Int), STDIO]
                   [STATE (Vect (n + m) Int), STDIO]
    readN Z = pure ()
    readN {m} (S k) = case !readInt of
                          True => rewrite plusSuccRightSucc k m in readN k
                          False => readN (S k)

The ``case`` analysis on the result of ``readInt`` means that we know in
each branch whether reading the integer succeeded, and therefore how
many values still need to be read into the vector. What this means in
practice is that the type system has verified that a necessary dynamic
check (i.e. whether reading a value succeeded) has indeed been done.

.. note::
    Only ``case`` will work here. We cannot use ``if/then/else``
    because the ``then`` and ``else`` branches must have the same
    type. The ``case`` construct, however, abstracts over the value
    being inspected in the type of each branch.

File Management
===============

A practical use for dependent effects is in specifying resource usage
protocols and verifying that they are executed correctly. For example,
file management follows a resource usage protocol with the following
(informally specified) requirements:

-  It is necessary to open a file for reading before reading it

-  Opening may fail, so the programmer should check whether opening was
   successful

-  A file which is open for reading must not be written to, and vice
   versa

-  When finished, an open file handle should be closed

-  When a file is closed, its handle should no longer be used

These requirements can be expressed formally in , by creating a
``FILE_IO`` effect parameterised over a file handle state, which is
either empty, open for reading, or open for writing. The ``FILE_IO``
effect’s definition is given below. Note that this
effect is mainly for illustrative purposes—typically we would also like
to support random access files and better reporting of error conditions.

.. code-block:: idris

    module Effect.File

    import Effects
    import Control.IOExcept

    FILE_IO : Type -> EFFECT

    data OpenFile : Mode -> Type

    open : (fname : String)
           -> (m : Mode)
           -> Eff Bool [FILE_IO ()] 
                       (\res => [FILE_IO (case res of
                                               True => OpenFile m
                                               False => ())])
    close : Eff () [FILE_IO (OpenFile m)] [FILE_IO ()]

    readLine  : Eff String [FILE_IO (OpenFile Read)]
    writeLine : String -> Eff () [FILE_IO (OpenFile Write)]
    eof       : Eff Bool [FILE_IO (OpenFile Read)]

    Handler FileIO IO where { ... }

In particular, consider the type of ``open``:

.. code-block:: idris

    open : (fname : String)
           -> (m : Mode)
           -> Eff Bool [FILE_IO ()] 
                       (\res => [FILE_IO (case res of
                                               True => OpenFile m
                                               False => ())])

This returns a ``Bool`` which indicates whether opening the file was
successful. The resulting state depends on whether the operation was
successful; if so, we have a file handle open for the stated purpose,
and if not, we have no file handle. By ``case`` analysis on the result,
we continue the protocol accordingly.

.. _eff-readfile:
.. code-block:: idris

    readFile : Eff (List String) [FILE_IO (OpenFile Read)]
    readFile = readAcc [] where
        readAcc : List String -> Eff (List String) [FILE_IO (OpenFile Read)] 
        readAcc acc = if (not !eof)
                         then readAcc (!readLine :: acc)
                         else pure (reverse acc)

Given a function ``readFile``, above, which reads from
an open file until reaching the end, we can write a program which opens
a file, reads it, then displays the contents and closes it, as follows,
correctly following the protocol:

.. code-block:: idris

    dumpFile : String -> Eff () [FILE_IO (), STDIO]
    dumpFile name = case !(open name Read) of
                        True => do putStrLn (show !readFile)
                                   close
                        False => putStrLn ("Error!")

The type of ``dumpFile``, with ``FILE_IO ()`` in its effect list,
indicates that any use of the file resource will follow the protocol
correctly (i.e. it both begins and ends with an empty resource). If we
fail to follow the protocol correctly (perhaps by forgetting to close
the file, failing to check that ``open`` succeeded, or opening the file
for writing) then we will get a compile-time error. For example,
changing ``open name Read`` to ``open name Write`` yields a compile-time
error of the following form:

::

    FileTest.idr:16:18:When elaborating right hand side of Main.case
    block in testFile:
    Can't solve goal
            SubList [(FILE_IO (OpenFile Read))]
                    [(FILE_IO (OpenFile Write)), STDIO]

In other words: when reading a file, we need a file which is open for
reading, but the effect list contains a ``FILE_IO`` effect carrying a
file open for writing.

Pattern-matching bind
=====================

It might seem that having to test each potentially failing operation
with a ``case`` clause could lead to ugly code, with lots of
nested case blocks. Many languages support exceptions to improve this,
but unfortunately exceptions may not allow completely clean resource
management—for example, guaranteeing that any ``open`` which did succeed
has a corresponding close.

Idris supports *pattern-matching* bindings, such as the following:

.. code-block:: idris

    dumpFile : String -> Eff () [FILE_IO (), STDIO]
    dumpFile name = do True <- open name Read
                       putStrLn (show !readFile)
                       close

This also has a problem: we are no longer dealing with the case where
opening a file failed! The solution is to extend the pattern-matching
binding syntax to give brief clauses for failing matches. Here, for
example, we could write:

.. code-block:: idris

    dumpFile : String -> Eff () [FILE_IO (), STDIO]
    dumpFile name  = do True <- open name Read | False => putStrLn "Error"
                        putStrLn (show !readFile)
                        close

This is exactly equivalent to the definition with the explicit ``case``.
In general, in a ``do``-block, the syntax:

.. code-block:: idris

    do pat <- val | <alternatives>
       p

is desugared to

.. code-block:: idris

    do x <- val
       case x of
            pat => p
            <alternatives>

There can be several ``alternatives``, separated by a vertical bar
``|``. For example, there is a ``SYSTEM`` effect which supports
reading command line arguments, among other things (see Appendix
:ref:`sect-appendix`). To read command line arguments, we can use
``getArgs``:

.. code-block:: idris

    getArgs : Eff (List String) [SYSTEM]

A main program can read command line arguments as follows, where in the
list which is returned, the first element ``prog`` is the executable
name and the second is an expected argument:

.. code-block:: idris

    emain : Eff () [SYSTEM, STDIO]
    emain = do [prog, arg] <- getArgs
               putStrLn $ "Argument is " ++ arg
               {- ... rest of function ... -}

Unfortunately, this will not fail gracefully if no argument is given, or
if too many arguments are given. We can use pattern matching bind
alternatives to give a better (more informative) error:

.. code-block:: idris

    emain : Eff () [SYSTEM, STDIO]
    emain = do [prog, arg] <- getArgs | [] => putStrLn "Can't happen!"
                                      | [prog] => putStrLn "No arguments!"
                                      | _ => putStrLn "Too many arguments!"
               putStrLn $ "Argument is " ++ arg
               {- ... rest of function ... -}

If ``getArgs`` does not return something of the form ``[prog, arg]`` the
alternative which does match is executed instead, and that value
returned.
