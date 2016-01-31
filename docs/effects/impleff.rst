.. _sect-impleff:

********************
Creating New Effects
********************

We have now seen several side-effecting operations provided by the
``Effects`` library, and examples of their use in Section
:ref:`sect-simpleff`. We have also seen how operations may *modify*
the available effects by changing state in Section
:ref:`sect-depeff`. We have not, however, yet seen how these
operations are implemented. In this section, we describe how a
selection of the available effects are implemented, and show how new
effectful operations may be provided.

State
=====

Effects are described by *algebraic data types*, where the
constructors describe the operations provided when the effect is
available. Stateful operations are described as follows:

.. code-block:: idris

    data State : Effect where
         Get :      State a  a (\x => a)
         Put : b -> State () a (\x => b)

``Effect`` itself is a type synonym, giving the required type for an
effect signature:

.. code-block:: idris

    Effect : Type
    Effect = (result : Type) ->
             (input_resource : Type) ->
             (output_resource : result -> Type) -> Type

Each effect is associated with a *resource*. The second argument to
an effect signature is the resource type on *input* to an operation,
and the third is a function which computes the resource type on
*output*. Here, it means:

- ``Get`` takes no arguments. It has a resource of type ``a``, which is not updated, and running the ``Get`` operation returns something of type ``a``.

- ``Put`` takes a ``b`` as an argument. It has a resource of type ``a`` on input, which is updated to a resource of type ``b``. Running the ``Put`` operation returns the element of the unit type.

The effects library provides an overloaded function ``sig``
which can make effect signatures more concise, particularly when the
result has no effect on the resource type. For ``State``, we can
write:

.. code-block:: idris

    data State : Effect where
         Get :      sig State a  a
         Put : b -> sig State () a b

There are four versions of ``sig``, depending on whether we
are interested in the resource type, and whether we are updating the
resource. Idris will infer the appropriate version from usage.

.. code-block:: idris

    NoResourceEffect.sig : Effect -> Type -> Type
    NoUpdateEffect.sig   : Effect -> (ret : Type) -> 
                                     (resource : Type) -> Type
    UpdateEffect.sig     : Effect -> (ret : Type) -> 
                                     (resource_in : Type) -> 
                                     (resource_out : Type) -> Type
    DepUpdateEffect.sig  : Effect -> (ret : Type) -> 
                                     (resource_in : Type) -> 
                                     (resource_out : ret -> Type) -> Type

In order to convert ``State`` (of type ``Effect``) into something
usable in an effects list, of type ``EFFECT``, we write the following:

.. code-block:: idris

    STATE : Type -> EFFECT
    STATE t = MkEff t State

``MkEff`` constructs an ``EFFECT`` by taking the resource type (here,
the ``t`` which parameterises ``STATE``) and the effect signature
(here, ``State``). For reference, ``EFFECT`` is declared as follows:

.. code-block:: idris

    data EFFECT : Type where
         MkEff : Type -> Effect -> EFFECT

Recall that to run an effectful program in ``Eff``, we use one of the
``run`` family of functions to run the program in a particular
computation context ``m``. For each effect, therefore, we must explain
how it is executed in a particular computation context for ``run`` to
work in that context. This is achieved with the following interface:

.. code-block:: idris

    interface Handler (e : Effect) (m : Type -> Type) where
          handle : resource -> (eff : e t resource resource') ->
                   ((x : t) -> resource' x -> m a) -> m a

We have already seen some implementation declarations in the effect
summaries in Section :ref:`sect-simpleff`. An implementation of ``Handler e
m`` means that the effect declared with signature ``e`` can be run in
computation context ``m``. The ``handle`` function takes:

- The ``resource`` on input (so, the current value of the state for ``State``)

- The effectful operation (either ``Get`` or ``Put x`` for ``State``)

- A *continuation*, which we conventionally call ``k``, and should be passed the result value of the operation, and an updated resource.

There are two reasons for taking a continuation here: firstly, this is
neater because there are multiple return values (a new resource and
the result of the operation); secondly, and more importantly, the
continuation can be called zero or more times.

A ``Handler`` for ``State`` simply passes on the value of the state,
in the case of ``Get``, or passes on a new state, in the case of
``Put``.  It is defined the same way for all computation contexts:

.. code-block:: idris

    Handler State m where
         handle st Get     k = k st st
         handle st (Put n) k = k () n

This gives enough information for ``Get`` and ``Put`` to be used
directly in ``Eff`` programs. It is tidy, however, to define top level
functions in ``Eff``, as follows:

.. code-block:: idris

    get : Eff x [STATE x]
    get = call Get

    put : x -> Eff () [STATE x]
    put val = call (Put val)

    putM : y -> Eff () [STATE x] [STATE y]
    putM val = call (Put val)

**An implementation detail (aside):** The ``call`` function converts
an ``Effect`` to a function in ``Eff``, given a proof that the effect
is available. This proof can be constructed automatically by , since
it is essentially an index into a statically known list of effects:

.. code-block:: idris

    call : {e : Effect} ->
           (eff : e t a b) -> {auto prf : EffElem e a xs} ->
           Eff t xs (\v => updateResTy v xs prf eff)

This is the reason for the ``Can’t solve goal`` error when an effect
is not available: the implicit proof ``prf`` has not been solved
automatically because the required effect is not in the list of
effects ``xs``.

Such details are not important for using the library, or even writing
new effects, however.

Summary
-------

The following listing summarises what is required to define the
``STATE`` effect:

.. code-block:: idris

    data State : Effect where
         Get :      sig State a  a
         Put : b -> sig State () a b

    STATE : Type -> EFFECT
    STATE t = MkEff t State

    Handler State m where
         handle st Get     k = k st st
         handle st (Put n) k = k () n

    get : Eff x [STATE x]
    get = call Get

    put : x -> Eff () [STATE x]
    put val = call (Put val)

    putM : y -> Eff () [STATE x] [STATE y]
    putM val = call (Put val)


Console I/O
===========

Then listing below gives the definition of the ``STDIO``
effect, including handlers for ``IO`` and ``IOExcept``. We omit the
definition of the top level ``Eff`` functions, as this merely invoke
the effects ``PutStr``, ``GetStr``, ``PutCh`` and ``GetCh`` directly.

Note that in this case, the resource is the unit type in every case,
since the handlers merely apply the ``IO`` equivalents of the effects
directly.

.. _eff-stdiodef:
.. code-block:: idris

    data StdIO : Effect where
         PutStr : String -> sig StdIO ()
         GetStr : sig StdIO String
         PutCh : Char -> sig StdIO ()
         GetCh : sig StdIO Char

    Handler StdIO IO where
        handle () (PutStr s) k = do putStr s; k () ()
        handle () GetStr     k = do x <- getLine; k x ()
        handle () (PutCh c)  k = do putChar c; k () ()
        handle () GetCh      k = do x <- getChar; k x ()

    Handler StdIO (IOExcept a) where
        handle () (PutStr s) k = do ioe_lift $ putStr s; k () ()
        handle () GetStr     k = do x <- ioe_lift $ getLine; k x ()
        handle () (PutCh c)  k = do ioe_lift $ putChar c; k () ()
        handle () GetCh      k = do x <- ioe_lift $ getChar; k x ()

    STDIO : EFFECT
    STDIO = MkEff () StdIO

Exceptions
==========

The listing below gives the definition of the ``Exception``
effect, including two of its handlers for ``Maybe`` and ``List``. The
only operation provided is ``Raise``. The key point to note in the
definitions of these handlers is that the continuation ``k`` is not
used. Running ``Raise`` therefore means that computation stops with an
error.

.. code-block:: idris

    data Exception : Type -> Effect where
         Raise : a -> sig (Exception a) b

    Handler (Exception a) Maybe where
         handle _ (Raise e) k = Nothing

    Handler (Exception a) List where
         handle _ (Raise e) k = []

    EXCEPTION : Type -> EFFECT
    EXCEPTION t = MkEff () (Exception t)


Non-determinism
===============

The following listing gives the definition of the ``Select``
effect for writing non-deterministic programs, including a handler for
``List`` context which returns all possible successful values, and a
handler for ``Maybe`` context which returns the first successful
value.

.. code-block:: idris

    data Selection : Effect where
         Select : List a -> sig Selection a

    Handler Selection Maybe where
         handle _ (Select xs) k = tryAll xs where
             tryAll [] = Nothing
             tryAll (x :: xs) = case k x () of
                                     Nothing => tryAll xs
                                     Just v => Just v

    Handler Selection List where
         handle r (Select xs) k = concatMap (\x => k x r) xs

    SELECT : EFFECT
    SELECT = MkEff () Selection


Here, the continuation is called multiple times in each handler, for
each value in the list of possible values. In the ``List`` handler, we
accumulate all successful results, and in the ``Maybe`` handler we try
the first value in the list, and try later values only if that fails.

File Management
===============

Result-dependent effects are no different from non-dependent effects
in the way they are implemented. The listing below
illustrates this for the ``FILE_IO`` effect. The syntax for state
transitions ``{ x ==> {res} x’ }``, where the result state ``x’`` is
computed from the result of the operation ``res``, follows that for
the equivalent ``Eff`` programs.

.. code-block:: idris

    data FileIO : Effect where
         Open : (fname: String)
                -> (m : Mode)
                -> sig FileIO Bool () (\res => case res of
                                                    True => OpenFile m
                                                    False => ())
         Close : sig FileIO () (OpenFile m)

         ReadLine  :           sig FileIO String (OpenFile Read)
         WriteLine : String -> sig FileIO ()     (OpenFile Write)
         EOF       :           sig FileIO Bool   (OpenFile Read)

    Handler FileIO IO where
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

Note that in the handler for ``Open``, the types passed to the
continuation ``k`` are different depending on whether the result is
``True`` (opening succeeded) or ``False`` (opening failed). This uses
``validFile``, defined in the ``Prelude``, to test whether a file
handler refers to an open file or not.
