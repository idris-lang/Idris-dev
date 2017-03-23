.. _composing:

************************
Composing State Machines 
************************

In the previous section, we defined a ``DataStore`` interface and used it
to implement the following small program which allows a user to log in to
the store then display the store's contents;

.. code-block:: idris

  getData : (ConsoleIO m, DataStore m) => ST m () []
  getData = do st <- connect
               OK <- login st
                  | BadPassword => do putStrLn "Failure"
                                      disconnect st
               secret <- readSecret st
               putStrLn ("Secret is: " ++ show secret)
               logout st
               disconnect st

This function only uses one state, the store itself. Usually, though,
larger programs have lots of states, and might add, delete and update
states over the course of its execution. Here, for example, a useful
extension might be to loop forever, keeping count of the number of times
there was a login failure in a state.

Furthermore, we may have *hierarchies* of state machines, in that one
state machine could be implemented by composing several others. For
example, we can have a state machine representing the state of a 
graphics system, and use this to implement a *higher level* graphics API
such as turtle graphics, which uses the graphics system plus some additional
state for the turtle.

In this section, we'll see how to work with multiple states, and how to
compose state machines to make higher level state machines. We'll begin by
seeing how to add a login failure counter to ``getData``.

Working with multiple resources
===============================

To see how to work with multiple resources, we'll modify ``getData`` so
that it loops, and counts the total number of times the user fails to
log in. For example, if we write a ``main`` program which initialises the
count to zero, a session might run as follows:

.. code::

    *LoginCount> :exec main
    Enter password: Mornington Crescent
    Secret is: "Secret Data"
    Enter password: Dollis Hill 
    Failure
    Number of failures: 1
    Enter password: Mornington Crescent
    Secret is: "Secret Data"
    Enter password: Codfanglers
    Failure
    Number of failures: 2
    ...

We'll start by adding a state resource to ``getData`` to keep track of the
number of failures:

.. code-block:: idrs

  getData : (ConsoleIO m, DataStore m) =>
            (failcount : Var) -> ST m () [failcount ::: State Integer]

.. topic:: Type checking ``getData``

  If you're following along in the code, you'll find that ``getData``
  no longer compiles when you update this type. That is to be expected!
  For the moment, comment out the definition of ``getData``. We'll come back
  to it shortly.

Then, we can create a ``main`` program which initialises the state to ``0``
and invokes ``getData``, as follows:

.. code-block:: idris

  main : IO ()
  main = run (do fc <- new 0
                 getData fc
                 delete fc)

We'll start our implementation of ``getData`` just by adding the new
argument for the failure count:

.. code-block:: idris

  getData : (ConsoleIO m, DataStore m) =>
            (failcount : Var) -> ST m () [failcount ::: State Integer]
  getData failcount
          = do st <- connect
               OK <- login st
                  | BadPassword => do putStrLn "Failure"
                                      disconnect st
               secret <- readSecret st
               putStrLn ("Secret is: " ++ show secret)
               logout st
               disconnect st

Unfortunately, this doesn't type check, because we have the wrong resources
for calling ``connect``. The error messages shows how the resources don't
match:

.. code-block:: idris

    When checking an application of function Control.ST.>>=:
        Error in state transition:
                Operation has preconditions: []
                States here are: [failcount ::: State Integer]
                Operation has postconditions: \result => [result ::: Store LoggedOut] ++ []
                Required result states here are: st2_fn

In other words, ``connect`` requires that there are *no* resources on
entry, but we have *one*, the failure count!  
This shouldn't be a problem, though: the required resources are a *subset* of
the resources we have, after all, and the additional resources (here, the
failure count) are not relevant to ``connect``. What we need, therefore,
is a way to temporarily *hide* the additional resource.

We can achieve this with the ``call`` function:

.. code-block:: idris

  getData : (ConsoleIO m, DataStore m) =>
            (failcount : Var) -> ST m () [failcount ::: State Integer]
  getData failcount
     = do st <- call connect
          ?whatNow

Here we've left a hole for the rest of ``getData`` so that you can see the
effect of ``call``. It has removed the unnecessary parts of the resource
list for calling ``connect``, then reinstated them on return. The type of
``whatNow`` therefore shows that we've added a new resource ``st``, and still
have ``failcount`` available:

.. code-block:: idris

      failcount : Var
      m : Type -> Type
      constraint : ConsoleIO m
      constraint1 : DataStore m
      st : Var
    --------------------------------------
    whatNow : STrans m () [failcount ::: State Integer, st ::: Store LoggedOut]
                          (\result => [failcount ::: State Integer])

By the end of the function, ``whatNow`` says that we need to have finished with
``st``, but still have ``failcount`` available. We can complete ``getData``
so that it works with an additional state resource by adding ``call`` whenever
we invoke one of the operations on the data store, to reduce the list of
resources:

.. code-block:: idris

  getData : (ConsoleIO m, DataStore m) =>
            (failcount : Var) -> ST m () [failcount ::: State Integer]
  getData failcount
          = do st <- call connect
               OK <- call $ login st
                  | BadPassword => do putStrLn "Failure"
                                      call $ disconnect st
               secret <- call $ readSecret st
               putStrLn ("Secret is: " ++ show secret)
               call $ logout st
               call $ disconnect st

This is a little noisy, and in fact we can remove the need for it by
making ``call`` implicit. By default, you need to add the ``call`` explicitly,
but if you import ``Control.ST.ImplicitCall``, Idris will insert ``call``
where it is necessary.

.. code-block:: idris

  import Control.ST.ImplicitCall

It's now possible to write ``getData`` exactly as before:

.. code-block:: idris

  getData : (ConsoleIO m, DataStore m) =>
            (failcount : Var) -> ST m () [failcount ::: State Integer]
  getData failcount
          = do st <- connect
               OK <- login st
                  | BadPassword => do putStrLn "Failure"
                                      disconnect st
               secret <- readSecret st
               putStrLn ("Secret is: " ++ show secret)
               logout st
               disconnect st

There is a trade off here: if you import ``Control.ST.ImplicitCall`` then
functions which use multiple resources are much easier to read, because the
noise of ``call`` has gone. On the other hand, Idris has to work a little
harder to type check your functions, and as a result it can take slightly
longer, and the error messages can be less helpful.

It is instructive to see the type of ``call``:

.. code-block:: idris

    call : STrans m t sub new_f -> {auto res_prf : SubRes sub old} ->
           STrans m t old (\res => updateWith (new_f res) old res_prf)

The function being called has a list of resources ``sub``, and
there is an implicit proof, ``SubRes sub old`` that the resource list in
the function being called is a subset of the overall resource list. The
ordering of resources is allowed to change, although resources which
appear in ``old`` can't appear in the ``sub`` list more than once (you will
get a type error if you try this).

The function ``updateWith`` takes the *output* resources of the 
called function, and updates them in the current resource list. It makes
an effort to preserve ordering as far as possible, although this isn't
always possible if the called function does some complicated resource
manipulation.

.. topic:: Newly created resources in called functions

   If the called function creates any new resources, these will typically
   appear at the *end* of the resource list, due to the way ``updateWith``
   works. You can see this in the type of ``whatNow`` in our incomplete
   definition of ``getData`` above.

Finally, we can update ``getData`` so that it loops, and keeps
``failCount`` updated as necessary:

.. code-block:: idris

  getData : (ConsoleIO m, DataStore m) =>
            (failcount : Var) -> ST m () [failcount ::: State Integer]
  getData failcount
     = do st <- call connect
          OK <- login st
             | BadPassword => do putStrLn "Failure"
                                 fc <- read failcount
                                 write failcount (fc + 1)
                                 putStrLn ("Number of failures: " ++ show (fc + 1))
                                 disconnect st
                                 getData failcount
          secret <- readSecret st
          putStrLn ("Secret is: " ++ show secret)
          logout st
          disconnect st
          getData failcount

Note that here, we're connecting and disconnecting on every iteration.
Another way to implement this would be to ``connect`` first, then call
``getData``, and implement ``getData`` as follows:

.. code-block:: idris

  getData : (ConsoleIO m, DataStore m) =>
            (st, failcount : Var) -> ST m () [st ::: Store {m} LoggedOut, failcount ::: State Integer]
  getData st failcount
     = do OK <- login st
             | BadPassword => do putStrLn "Failure"
                                 fc <- read failcount
                                 write failcount (fc + 1)
                                 putStrLn ("Number of failures: " ++ show (fc + 1))
                                 getData st failcount
          secret <- readSecret st
          putStrLn ("Secret is: " ++ show secret)
          logout st
          getData st failcount

It is important to add the explicit ``{m}`` in the type of ``Store {m}
LoggedOut`` for ``st``, because this gives Idris enough information to know
which implementation of ``DataStore`` to use to find the appropriate
implementation for ``Store``. Otherwise, if we only write ``Store LoggedOut``,
there's no way to know that the ``Store`` is linked with the computation
context ``m``.

We can then ``connect`` and ``disconnect`` only once, in ``main``:

.. code-block:: idris

  main : IO ()
  main = run (do fc <- new 0
                 st <- connect
                 getData st fc
                 disconnect st
                 delete fc)

By using ``call``, and importing ``Control.ST.ImplicitCall``, we can
write programs which use multiple resources, and reduce the list of
resources as necessary when calling functions which only use a subset of
the overall resources.

Composite resources: Hierarchies of state machines
==================================================

Composite resources: Graphics


