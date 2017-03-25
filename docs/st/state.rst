.. _introst:

**********************************
Introducing ST: Working with State
**********************************

The ``Control.ST`` library provides facilities for creating, reading, writing
and destroying state in Idris functions, and tracking changes of state in
a function's type. It is based around the concept of *resources*, which are,
essentially, mutable variables, and a dependent type, ``STrans`` which tracks
how those resources change when a function runs:

.. code-block:: idris

    STrans : (m : Type -> Type) ->
             (resultType : Type) ->
             (in_res : Resources) ->
             (out_res : resultType -> Resources) ->
             Type

A value of type ``STrans m resultType in_res out_res_fn`` represents a sequence
of actions which can manipulate state. The arguments are: 

* ``m``, which is an underlying *computation context* in which the actions will be executed.
  Usually, this will be a generic type with a ``Monad`` implementation, but 
  it isn't necessarily so. In particular, there is no need to understand monads
  to be able to use ``ST`` effectively!
* ``resultType``, which is the type of the value the sequence will produce
* ``in_res``, which is a list of *resources* available *before* executing the actions.
* ``out_res``, which is a list of resources available *after* executing the actions,
  and may differ depending on the result of the actions.

We can use ``STrans`` to describe *state transition systems* in a function's
type. We'll come to the definition of ``Resources`` shortly, but for the moment
you can consider it an abstract representation of the "state of the world".
By giving the input resources (``in_res``) and the output resources
(``out_res``) we are describing the *preconditions* under which a function
is allowed to execute, and *postconditions* which describe how a function
affects the overall state of the world.

We'll begin in this section by looking at some small examples of ``STrans``
functions, and see how to execute them. We'll also introduce ``ST``,
a type-level function which allows us to describe the state transitions of
a stateful function concisely.

.. topic:: Type checking the examples

    For the examples in this section, and throughout this tutorial,
    you'll need to ``import Control.ST`` and add the ``contrib`` package by
    passing the ``-p contrib`` flag to ``idris``.


Introductory examples: manipulating ``State``
=============================================

An ``STrans`` function explains, in its type, how it affects a collection of
``Resources``. A resource has a *label* (of type ``Var``), which we use to
refer to the resource throughout the function, and we write the state of a
resource, in the ``Resources`` list, in the form ``label ::: type``.

For example, the following function
has a resource ``x`` available on input, of type ``State Integer``, and that
resource is still a ``State Integer`` on output:

.. code-block:: idris

  increment : (x : Var) -> STrans m () [x ::: State Integer]
                                       (const [x ::: State Integer])
  increment x = do num <- read x
                   write x (num + 1)

.. sidebar:: Verbosity of the type of ``increment``

    The type of ``increment`` may seem somewhat verbose, in that the
    *input* and *output* resources are repeated, even though they are the
    same. We'll introduce a much more concise way of writing this type at the
    end of this section (:ref:`sttype`), when we describe the ``ST`` type
    itself.
                   
This function reads the value stored at the resource ``x`` with ``read``,
increments it then writes the result back into the resource ``x`` with
``write``. We'll see the types of ``read`` and ``write`` shortly 
(see :ref:`stransprimops`). We can also create and delete resources:

.. code-block:: idris

  makeAndIncrement : Integer -> STrans m Integer [] (const [])
  makeAndIncrement init = do var <- new init
                             increment var
                             x <- read var
                             delete var
                             pure x

The type of ``makeAndIncrement`` states that it has *no* resources available on
entry (``[]``) or exit (``const []``). It creates a new ``State`` resource with
``new`` (which takes an initial value for the resource), increments the value,
reads it back, then deletes it using ``delete``, returning the final value
of the resource. Again, we'll see the types of ``new`` and ``delete``
shortly.

The ``m`` argument to ``STrans`` (of type ``Type -> Type``) is the *computation context* in
which the function can be run. Here, the type level variable indicates that we
can run it in *any* context. We can run it in the identity context with
``runPure``. For example, try entering the above definitions in a file
``Intro.idr`` then running the following at the REPL:

.. code:: 

    *Intro> runPure (makeAndIncrement 93)
    94 : Integer

It's a good idea to take an interactive, type-driven approach to implementing
``STrans`` programs. For example, after creating the resource with ``new init``,
you can leave a *hole* for the rest of the program to see how creating the
resource has affected the type:

.. code-block:: idris

  makeAndIncrement : Integer -> STrans m Integer [] (const [])
  makeAndIncrement init = do var <- new init
                             ?whatNext

If you check the type of ``?whatNext``, you'll see that there is now
a resource available, ``var``, and that by the end of the function there
should be no resource available:

.. code-block:: idris

      init : Integer
      m : Type -> Type
      var : Var
    --------------------------------------
    whatNext : STrans m Integer [var ::: State Integer] (\value => [])

These small examples work in any computation context ``m``. However, usually,
we are working in a more restricted context. For example, we might want to
write programs which only work in a context that supports interactive
programs. For this, we'll need to see how to *lift* operations from the
underlying context.

Lifting: Using the computation context
======================================

Let's say that, instead of passing an initial integer to ``makeAndIncrement``,
we want to read it in from the console. Then, instead of working in a generic
context ``m``, we can work in the specific context ``IO``:

.. code-block:: idris

    ioMakeAndIncrement : STrans IO () [] (const [])

This gives us access to ``IO`` operations, via the ``lift`` function. We
can define ``ioMakeAndIncrement`` as follows:

.. code-block:: idris

  ioMakeAndIncrement : STrans IO () [] (const [])
  ioMakeAndIncrement
     = do lift $ putStr "Enter a number: "
          init <- lift $ getLine
          var <- new (cast init)
          lift $ putStrLn ("var = " ++ show !(read var))
          increment var
          lift $ putStrLn ("var = " ++ show !(read var))
          delete var

The ``lift`` function allows us to use funtions from the underlying
computation context (``IO`` here) directly. Again, we'll see the exact type
of ``lift`` shortly.

.. topic:: !-notation

    In ``ioMakeAndIncrement`` we've used ``!(read var)`` to read from the
    resource. You can read about this ``!``-notation in the main Idris tutorial
    (see :ref:`monadsdo`). In short, it allows us to use an ``STrans``
    function inline, rather than having to bind the result to a variable
    first.

    Conceptually, at least, you can think of it as having the following type:

    .. code-block:: idris
    
        (!) : STrans m a state_in state_out -> a

    It is syntactic sugar for binding a variable immediately before the
    current action in a ``do`` block, then using that variable in place of
    the ``!``-expression.


In general, though, it's bad practice to use a *specific* context like
``IO``. Firstly, it requires us to sprinkle ``lift`` liberally throughout
our code, which hinders readability. Secondly, and more importantly, it will
limit the safety of our functions, as we'll see in the next section
(:ref:`smstypes`).

So, instead, we define *interfaces* to restrict the computation context.
For example, ``Control.ST`` defines a ``ConsoleIO`` interface which
provides the necessary methods for performing basic console interaction:

.. code-block:: idris

    interface ConsoleIO (m : Type -> Type) where
      putStr : String -> STrans m () res (const res)
      getStr : STrans m String res (const res)

That is, we can write to and read from the console with any available
resources ``res``, and neither will affect the available resources.
This has the following implementation for ``IO``:

.. code-block:: idris

    ConsoleIO IO where
      putStr str = lift (Interactive.putStr str)
      getStr = lift Interactive.getLine

Now, we can define ``ioMakeAndIncrement`` as follows:

.. code-block:: idris

  ioMakeAndIncrement : ConsoleIO io => STrans io () [] (const [])
  ioMakeAndIncrement
     = do putStr "Enter a number: "
          init <- getStr
          var <- new (cast init)
          putStrLn ("var = " ++ show !(read var))
          increment var
          putStrLn ("var = " ++ show !(read var))
          delete var

Instead of working in ``IO`` specifically, this works in a generic context
``io``, provided that there is an implementation of ``ConsoleIO`` for that
context. This has several advantages over the first version:

* All of the calls to ``lift`` are in the implementation of the interface,
  rather than ``ioMakeAndIncrement``
* We can provide alternative implementations of ``ConsoleIO``, perhaps
  supporting exceptions or logging in addition to basic I/O.
* As we'll see in the next section (:ref:`smstypes`), it will allow us to
  define safe APIs for manipulating specific resources more precisely.

Earlier, we used ``runPure`` to run ``makeAndIncrement`` in the identity
context. Here, we use ``run``, which allows us to execute an ``STrans`` program
in any context (as long as it has an implementation of ``Applicative``) and we
can execute ``ioMakeAndIncrement`` at the REPL as follows:

.. code:: 

    *Intro> :exec run ioMakeAndIncrement
    Enter a number: 93
    var = 93
    var = 94

.. _depstate:

Manipulating ``State`` with dependent types
===========================================

In our first example of ``State``, when we incremented the value its
*type* remained the same. However, when we're working with
*dependent* types, updating a state may also involve updating its type.
For example, if we're adding an element to a vector stored in a state,
its length will change:

.. code-block:: idris

  addElement : (vec : Var) -> (item : a) ->
               STrans m () [vec ::: State (Vect n a)]
                    (const [vec ::: State (Vect (S n) a)])
  addElement vec item = do xs <- read vec
                           write vec (item :: xs)

Note that you'll need to ``import Data.Vect`` to try this example. 

.. topic:: Updating a state directly with ``update``

    Rather than using ``read`` and ``write`` separately, you can also
    use ``update`` which reads from a ``State``, applies a function to it,
    then writes the result. Using ``update`` you could write ``addElement``
    as follows:

    .. code-block:: idris

      addElement : (vec : Var) -> (item : a) ->
                   STrans m () [vec ::: State (Vect n a)]
                        (const [vec ::: State (Vect (S n) a)])
      addElement vec item = update vec (item ::)

We don't always know *how* exactly the type will change in the course of a
sequence actions, however. For example, if we have a state containing a
vector of integers, we might read an input from the console and only add it
to the vector if the input is a valid integer. Somehow, we need a different
type for the output state depending on whether reading the integer was
successful, so neither of the following types is quite right:

.. code-block:: idris

  readAndAdd_OK : ConsoleIO io => (vec : Var) ->
                  STrans m ()  -- Returns an empty tuple
                              [vec ::: State (Vect n Integer)]
                       (const [vec ::: State (Vect (S n) Integer)])
  readAndAdd_Fail : ConsoleIO io => (vec : Var) ->
                    STrans m ()  -- Returns an empty tuple
                                [vec ::: State (Vect n Integer)]
                         (const [vec ::: State (Vect n Integer)])

Remember, though, that the *output* resource types can be *computed* from
the result of a function. So far, we've used ``const`` to note that the
output resources are always the same, but here, instead, we can use a type
level function to *calculate* the output resources. We start by returning
a ``Bool`` instead of an empty tuple, which is ``True`` if reading the input
was successful, and leave a *hole* for the output resources:

.. code-block:: idris

  readAndAdd : ConsoleIO io => (vec : Var) ->
               STrans m Bool [vec ::: State (Vect n Integer)]
                             ?output_res

If you check the type of ``?output_res``, you'll see that Idris expects
a function of type ``Bool -> Resources``, meaning that the output resource
type can be different depending on the result of ``readAndAdd``:

.. code-block:: idris

      n : Nat
      m : Type -> Type
      io : Type -> Type
      constraint : ConsoleIO io
      vec : Var
    --------------------------------------
    output_res : Bool -> Resources

So, the output resource is either a ``Vect n Integer`` if the input is
invalid (i.e. ``readAndAdd`` returns ``False``) or a ``Vect (S n) Integer``
if the input is valid. We can express this in the type as follows:

.. code-block:: idris

  readAndAdd : ConsoleIO io => (vec : Var) ->
               STrans io Bool [vec ::: State (Vect n Integer)]
                     (\res => [vec ::: State (if res then Vect (S n) Integer
                                                     else Vect n Integer)])

Then, when we implement ``readAndAdd`` we need to return the appropriate
value for the output state. If we've added an item to the vector, we need to
return ``True``, otherwise we need to return ``False``:
                                                     
.. code-block:: idris

  readAndAdd : ConsoleIO io => (vec : Var) ->
               STrans io Bool [vec ::: State (Vect n Integer)]
                     (\res => [vec ::: State (if res then Vect (S n) Integer
                                                     else Vect n Integer)])
  readAndAdd vec = do putStr "Enter a number: "
                      num <- getStr
                      if all isDigit (unpack num)
                         then do
                           update vec ((cast num) ::)
                           pure True     -- added an item, so return True
                         else pure False -- didn't add, so return False

There is a slight difficulty if we're developing interactively, which is
that if we leave a hole, the required output state isn't easily visible
until we know the value that's being returned. For example. in the following
incomplete definition of ``readAndAdd`` we've left a hole for the
successful case:

.. code-block:: idris

  readAndAdd vec = do putStr "Enter a number: "
                      num <- getStr
                      if all isDigit (unpack num)
                         then ?whatNow
                         else pure False

We can look at the type of ``?whatNow``, but it is unfortunately rather less
than informative:

.. code-block:: idris

      vec : Var
      n : Nat
      io : Type -> Type
      constraint : ConsoleIO io
      num : String
    --------------------------------------
    whatNow : STrans io Bool [vec ::: State (Vect (S n) Integer)]
                     (\res =>
                        [vec :::
                         State (ifThenElse res
                                           (Delay (Vect (S n) Integer))
                                           (Delay (Vect n Integer)))])

The problem is that we'll only know the required output state when we know
the value we're returning. To help with interactive development, ``Control.ST``
provides a function ``returning`` which allows us to specify the return
value up front, and to update the state accordingly. For example, we can
write an incomplete ``readAndAdd`` as follows:

.. code-block:: idris

  readAndAdd vec = do putStr "Enter a number: "
                      num <- getStr
                      if all isDigit (unpack num)
                         then returning True ?whatNow
                         else pure False

This states that, in the successful branch, we'll be returning ``True``, and
``?whatNow`` should explain how to update the states appropriately so that
they are correct for a return value of ``True``. We can see this by checking
the type of ``?whatNow``, which is now a little more informative:

.. code-block:: idris

      vec : Var
      n : Nat
      io : Type -> Type
      constraint : ConsoleIO io
      num : String
    --------------------------------------
    whatnow : STrans io () [vec ::: State (Vect n Integer)]
                     (\value => [vec ::: State (Vect (S n) Integer)])

This type now shows, in the output resource list of ``STrans``,
that we can complete the definition by adding an item to ``vec``, which
we can do as follows:

.. code-block:: idris

  readAndAdd vec = do putStr "Enter a number: "
                      num <- getStr
                      if all isDigit (unpack num)
                         then returning True (update vec ((cast num) ::))
                         else returning False (pure ()) -- returning False, so no state update required

.. _stransprimops:

``STrans`` Primitive operations 
===============================

Now that we've written a few small examples of ``STrans`` functions, it's
a good time to look more closely at the types of the state manipulation
functions we've used. First, to read and write states, we've used
``read`` and ``write``:

.. code-block:: idris

    read : (lbl : Var) -> {auto prf : InState lbl (State ty) res} ->
           STrans m ty res (const res)
    write : (lbl : Var) -> {auto prf : InState lbl ty res} ->
            (val : ty') ->
            STrans m () res (const (updateRes res prf (State ty')))

These types may look a little daunting at first, particularly due to the
implicit ``prf`` argument, which has the following type:

.. code-block:: idris

    prf : InState lbl (State ty) res}

This relies on a predicate ``InState``. A value of type ``InState x ty res``
means that the reference ``x`` must have type ``ty`` in the list of
resources ``res``. So, in practice, all this type means is that we can
only read or write a resource if a reference to it exists in the list of
resources.

Given a resource label ``res``, and a proof that ``res`` exists in a list
of resources, ``updateRes`` will update the type of that resource. So,
the type of ``write`` states that the type of the resource will be updated
to the type of the given value.

The type of ``update`` is similar to that for ``read`` and ``write``, requiring
that the resource has the input type of the given function, and updating it to
have the output type of the function:

.. code-block:: idris

    update : (lbl : Var) -> {auto prf : InState lbl (State ty) res} ->
             (ty -> ty') ->
             STrans m () res (const (updateRes res prf (State ty')))

The type of ``new`` states that it returns a ``Var``, and given an initial
value of type ``state``, the output resources contains a new resource
of type ``State state``:

.. code-block:: idris

    new : (val : state) -> 
          STrans m Var res (\lbl => (lbl ::: State state) :: res)

It's important that the new resource has type ``State state``, rather than
merely ``state``, because this will allow us to hide implementation details
of APIs. We'll see more about what this means in the next section,
:ref:`smstypes`.

The type of ``delete`` states that the given label will be removed from
the list of resources, given an implicit proof that the label exists in
the input resources:

.. code-block:: idris

    delete : (lbl : Var) -> {auto prf : InState lbl (State st) res} ->
             STrans m () res (const (drop res prf))

Here, ``drop`` is a type level function which updates the resource list,
removing the given resource ``lbl`` from the list.

We've used ``lift`` to run functions in the underlying context. It has the
following type:

.. code-block:: idris

    lift : Monad m => m t -> STrans m t res (const res)

Given a ``result`` value, ``pure`` is an ``STrans`` program which produces
that value, provided that the current list of resources is correct when
producing that value:

.. code-block:: idris

    pure : (result : ty) -> STrans m ty (out_fn result) out_fn

We can use ``returning`` to break down returning a value from an
``STrans`` functions into two parts: providing the value itself, and updating
the resource list so that it is appropriate for returning that value:

.. code-block:: idris

    returning : (result : ty) -> 
                STrans m () res (const (out_fn result)) ->
                STrans m ty res out_fn

Finally, we've used ``run`` and ``runPure`` to execute ``STrans`` functions
in a specific context. ``run`` will execute a function in any context,
provided that there is an ``Applicative`` implementation for that context,
and ``runPure`` will execute a function in the identity context:

.. code-block:: idris

    run : Applicative m => STrans m a [] (const []) -> m a
    runPure : STrans Basics.id a [] (const []) -> a

Note that in each case, the input and output resource list must be empty.
There's no way to provide an initial resource list, or extract the final
resources. This is deliberate: it ensures that *all* resource management is
carried out in the controlled ``STrans`` environment and, as we'll see, this
allows us to implement safe APIs with precise types explaining exactly how
resources are tracked throughout a program.

These functions provide the core of the ``ST`` library; there are some
others which we'll encounter later, for more advanced situations, but the
functions we have seen so far already allow quite sophisticated state-aware
programming and reasoning in Idris.

.. _sttype:

`ST`: Representing state transitions directly
============================================

We've seen a few examples of small ``STrans`` functions now, and
their types can become quite verbose given that we need to provide explicit
input and output resource lists. This is convenient for giving types for
the primitive operations, but for more general use it's much more convenient
to be able to express *transitions* on individual resources, rather than
giving input and output resource lists in full. We can do this with
``ST``:

.. code-block:: idris

    ST : (m : Type -> Type) ->
         (resultType : Type) -> 
         List (Action resultType) -> Type

``ST`` is a type level function which computes an appropriate ``STrans``
type given a list of *actions*, which describe transitions on resources.
An ``Action`` in a function type can take one of the following forms (plus
some others which we'll see later in the tutorial):

* ``lbl ::: ty`` expresses that the resource ``lbl`` begins and ends in
  the state ``ty``
* ``lbl ::: ty_in :-> ty_out`` expresses that the resource ``lbl`` begins
  in state ``ty_in`` and ends in state ``ty_out``
* ``lbl ::: ty_in :-> (\res -> ty_out)`` expresses that the resource ``lbl``
  begins in state ``ty_in`` and ends in a state ``ty_out``, where ``ty_out``
  is computed from the result of the function ``res``.

So, we can write some of the function types we've seen so far as follows:

.. code-block:: idris

  increment : (x : Var) -> ST m () [x ::: State Integer]

That is, ``increment`` begins and ends with ``x`` in state ``State Integer``.

.. code-block:: idris
  
  makeAndIncrement : Int -> ST m Int []

That is, ``makeAndIncrement`` begins and ends with no resources.

.. code-block:: idris

  addElement : (vec : Var) -> (item : a) ->
               ST m () [vec ::: State (Vect n a) :-> State (Vect (S n) a)]

That is, ``addElement`` changes ``vec`` from ``State (Vect n a)`` to
``State (Vect (S n) a)``.

.. code-block:: idris

  readAndAdd : ConsoleIO io => (vec : Var) ->
               ST io Bool
                     [vec ::: State (Vect n Integer) :->
                      \res => State (if res then Vect (S n) Integer
                                            else Vect n Integer)]

By writing the types in this way, we express the minimum necessary to explain
how each function affects the overall resource state. If there is a resource
update depending on a result, as with ``readAndAdd``, then we need to describe
it in full. Otherwise, as with ``increment`` and ``makeAndIncrement``, we can
write the input and output resource lists without repetition.

An ``Action`` can also describe *adding* and *removing* states:

* ``add ty``, assuming the operation returns a ``Var``, adds a new resource
  of type ``ty``.
* ``remove lbl ty`` expresses that the operation removes the resource named
  ``lbl``, beginning in state ``ty`` from the resource list.

So, for example, we can write:

.. code-block:: idris

  newState : ST m Var [add (State Int)]
  removeState : (lbl : Var) -> ST m () [remove lbl (State Int)]

The first of these, ``newState``, returns a new resource label, and adds that
resource to the list with type ``State Int``. The second, ``removeState``,
given a label ``lbl``, removes the resource from the list. These types are
equivalent to the following:

.. code-block:: idris

  newState : STrans m Var [] (\lbl => [lbl ::: State Int])
  removeState : (lbl : Var) -> STrans m () [lbl ::: State Int] (const [])

These are the primitive methods of constructing an ``Action``.  Later, we will
encounter some other ways using type level functions to help with readability.

In the remainder of this tutorial, we will generally use ``ST`` except on
the rare occasions we need the full precision of ``STrans``. In the next
section, we'll see how to use the facilities provided by ``ST`` to write
a precise API for a system with security properties: a data store requiring
a login.


