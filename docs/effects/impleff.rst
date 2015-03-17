.. _sect-impleff:

====================
Creating New Effects
====================

We have now seen several side-effecting operations provided by the
library, and examples of their use in Section :ref:`sect-simpleff`. We have
also seen how operations may *modify* the available effects by changing
state in Section :ref:`sect-depeff`. We have not, however, yet seen how these
operations are implemented. In this section, we describe how a selection
of the available effects are implemented, and show how new effectful
operations may be provided.

State
-----

Effects are described by *algebraic data types*, where the constructors
describe the operations provided when the effect is available. Stateful
operations are described as follows:

.. code-block:: idris

    data State : Effect where
         Get :      { a }       State a
         Put : b -> { a ==> b } State ()

Each effect is associated with a *resource*, the type of which is given
with the notation ``{ x ==> x’ }``. This notation gives the resource
type expected by each operation, and how it updates when the operation
is run. Here, it means:

-  ``Get`` takes no arguments. It has a resource of type ``a``, which is
   not updated, and running the ``Get`` operation returns something of
   type ``a``.

-  ``Put`` takes a ``b`` as an argument. It has a resource of type ``a``
   on input, which is updated to a resource of type ``b``. Running the
   ``Put`` operation returns the element of the unit type.

``Effect`` itself is a type synonym, declared as follows:

.. code-block:: idris

    Effect : Type
    Effect = (result : Type) ->
             (input_resource : Type) ->
             (output_resource : result -> Type) -> Type

That is, an effectful operation returns something of type ``result``,
has an input resource of type ``input_resource``, and a function
``output_resource`` which computes the output resource type from the
result. We use the same syntactic sugar as with ``Eff`` to make effect
declarations more readable. It is defined as follows in the library:

.. code-block:: idris

    syntax "{" [inst] "}" [eff] = eff inst (\result => inst)
    syntax "{" [inst] "==>" "{" {b} "}" [outst] "}" [eff]
           = eff inst (\b => outst)
    syntax "{" [inst] "==>" [outst] "}" [eff] = eff inst (\result => outst)

In order to convert ``State`` (of type ``Effect``) into something usable
in an effects list, of type ``EFFECT``, we write the following:

.. code-block:: idris

    STATE : Type -> EFFECT
    STATE t = MkEff t State

``MkEff`` constructs an ``EFFECT`` by taking the resource type (here,
the ``t`` which parameterises ``STATE``) and the effect signature (here,
``State``). For reference, ``EFFECT`` is declared as follows:

.. code-block:: idris

    data EFFECT : Type where
         MkEff : Type -> Effect -> EFFECT

Recall that to run an effectful program in ``Eff``, we use one of the
``run`` family of functions to run the program in a particular
computation context ``m``. For each effect, therefore, we must explain
how it is executed in a particular computation context for ``run`` to
work in that context. This is achieved with the following type class:

.. code-block:: idris

    class Handler (e : Effect) (m : Type -> Type) where
          handle : resource -> (eff : e t resource resource') ->
                   ((x : t) -> resource' x -> m a) -> m a

We have already seen some instance declarations in the effect summaries
in Section [sect:simpleff]. An instance of ``Handler e m`` means that
the effect declared with signature ``e`` can be run in computation
context ``m``. The ``handle`` function takes:

-  The ``resource`` on input (so, the current value of the state for
   ``State``)

-  The effectful operation (either ``Get`` or ``Put x`` for ``State``)

-  A *continuation*, which we conventionally call ``k``, and should be
   passed the result value of the operation, and an updated resource.

There are two reasons for taking a continuation here: firstly, this is
neater because there are multiple return values (a new resource and the
result of the operation); secondly, and more importantly, the
continuation can be called zero or more times.

A ``Handler`` for ``State`` simply passes on the value of the state, in
the case of ``Get``, or passes on a new state, in the case of ``Put``.
It is defined the same way for all computation contexts:

.. code-block:: idris

    instance Handler State m where
         handle st Get     k = k st st
         handle st (Put n) k = k () n

This gives enough information for ``Get`` and ``Put`` to be used
directly in ``Eff`` programs. It is tidy, however, to define top level
functions in ``Eff``, as follows:

.. code-block:: idris

    get : { [STATE x] } Eff x
    get = call Get

    put : x -> { [STATE x] } Eff ()
    put val = call (Put val)

    putM : y -> { [STATE x] ==> [STATE y] } Eff ()
    putM val = call (Put val)

**An implementation detail (aside):** The ``call`` function converts an
``Effect`` to a function in ``Eff``, given a proof that the effect is
available. This proof can be constructed automatically by , since it is
essentially an index into a statically known list of effects:

.. code-block:: idris

    call : {e : Effect} ->
           (eff : e t a b) -> {auto prf : EffElem e a xs} ->
           Eff t xs (\v => updateResTy v xs prf eff)

This is the reason for the ``Can’t solve goal`` error when an effect is
not available: the implicit proof ``prf`` has not been solved
automatically because the required effect is not in the list of effects
``xs``.

Such details are not important for using the library, or even writing
new effects, however.

Summary
~~~~~~~

Listing :ref:`eff-statedef` summarises what is required to define the
``STATE`` effect.

.. _eff-statedef:
.. code-block:: idris
    :caption: Complete State Effect Definition

    data State : Effect where
         Get :      { a }       State a
         Put : b -> { a ==> b } State ()

    STATE : Type -> EFFECT
    STATE t = MkEff t State

    instance Handler State m where
         handle st Get     k = k st st
         handle st (Put n) k = k () n

    get : { [STATE x] } Eff x
    get = call Get

    put : x -> { [STATE x] } Eff ()
    put val = call (Put val)

    putM : y -> { [STATE x] ==> [STATE y] } Eff ()
    putM val = call (Put val)


Console I/O
-----------

Listing :ref:`eff-stdiodef` gives the definition of the ``STDIO`` effect,
including handlers for ``IO`` and ``IOExcept``. We omit the definition
of the top level ``Eff`` functions, as this merely invoke the effects
``PutStr``, ``GetStr``, ``PutCh`` and ``GetCh`` directly.

Note that in this case, the resource is the unit type in every case,
since the handlers merely apply the ``IO`` equivalents of the effects
directly.

.. _eff-stdiodef:
.. code-block:: idris
    :caption: Console I/O Effect Definition

    data StdIO : Effect where
         PutStr : String -> { () } StdIO ()
         GetStr : { () } StdIO String
         PutCh : Char -> { () } StdIO ()
         GetCh : { () } StdIO Char

    instance Handler StdIO IO where
        handle () (PutStr s) k = do putStr s; k () ()
        handle () GetStr     k = do x <- getLine; k x ()
        handle () (PutCh c)  k = do putChar c; k () ()
        handle () GetCh      k = do x <- getChar; k x ()

    instance Handler StdIO (IOExcept a) where
        handle () (PutStr s) k = do ioe_lift $ putStr s; k () ()
        handle () GetStr     k = do x <- ioe_lift $ getLine; k x ()
        handle () (PutCh c)  k = do ioe_lift $ putChar c; k () ()
        handle () GetCh      k = do x <- ioe_lift $ getChar; k x ()

    STDIO : EFFECT
    STDIO = MkEff () StdIO

Exceptions
----------

.. _eff-exceptdef:
.. code-block:: idris
    :caption: Exception Effect Definition

    data Exception : Type -> Effect where
         Raise : a -> { () } Exception a b

    instance Handler (Exception a) Maybe where
         handle _ (Raise e) k = Nothing

    instance Handler (Exception a) List where
         handle _ (Raise e) k = []

    EXCEPTION : Type -> EFFECT
    EXCEPTION t = MkEff () (Exception t)

Listing :ref:`eff-exceptdef` gives the definition of the ``Exception``
effect, including two of its handlers for ``Maybe`` and ``List``. The
only operation provided is ``Raise``. The key point to note in the
definitions of these handlers is that the continuation ``k`` is not
used. Running ``Raise`` therefore means that computation stops with an
error.

Non-determinism
---------------

.. _eff-selectdef:
.. code-block:: idris
    :caption: Non-determinism Effect Definition

    data Selection : Effect where
         Select : List a -> { () } Selection a

    instance Handler Selection Maybe where
         handle _ (Select xs) k = tryAll xs where
             tryAll [] = Nothing
             tryAll (x :: xs) = case k x () of
                                     Nothing => tryAll xs
                                     Just v => Just v

    instance Handler Selection List where
         handle r (Select xs) k = concatMap (\x => k x r) xs

    SELECT : EFFECT
    SELECT = MkEff () Selection

Listing :ref:`eff-selectdef` gives the definition of the ``Select`` effect
for writing non-deterministic programs, including a handler for ``List``
context which returns all possible successful values, and a handler for
``Maybe`` context which returns the first successful value.

Here, the continuation is called multiple times in each handler, for
each value in the list of possible values. In the ``List`` handler, we
accumulate all successful results, and in the ``Maybe`` handler we try
the first value in the last, and try later values only if that fails.

File Management
---------------

Result-dependent effects are no different from non-dependent effects in
the way they are implemented. Listing :ref:`eff-filedef` illustrates this for
the ``FILE_IO`` effect. The syntax for state transitions
``{ x ==> {res} x’ }``, where the result state ``x’`` is computed from
the result of the operation ``res``, follows that for the equivalent
``Eff`` programs.

Note that in the handler for ``Open``, the types passed to the
continuation ``k`` are different depending on whether the result is
``True`` (opening succeeded) or ``False`` (opening failed). This uses
``validFile``, defined in the ``Prelude``, to test whether a file
handler refers to an open file or not.

.. _eff-filedef:
.. code-block:: idris
    :caption: File I/O Effect Definition

    data FileIO : Effect where
         Open  : String -> (m : Mode) ->
                 {() ==> {res} if res then OpenFile m else ()} FileIO Bool
         Close : {OpenFile m ==> ()}                           FileIO ()

         ReadLine  :           {OpenFile Read}  FileIO String
         WriteLine : String -> {OpenFile Write} FileIO ()
         EOF       :           {OpenFile Read}  FileIO Bool

    instance Handler FileIO IO where
        handle () (Open fname m) k = do h <- openFile fname m
                                        if !(validFile h)
                                                 then k True (FH h)
                                                 else k False ()
        handle (FH h) Close      k = do closeFile h
                                        k () ()

        handle (FH h) ReadLine        k = do str <- fread h
                                             k str (FH h)
        handle (FH h) (WriteLine str) k = do fwrite h str
                                             k () (FH h)
        handle (FH h) EOF             k = do e <- feof h
                                             k e (FH h)

    FILE_IO : Type -> EFFECT
    FILE_IO t = MkEff t FileIO
