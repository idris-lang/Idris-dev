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

We've now seen how to use multiple resources in one function, which is
necessary for any realistic program which manipulates state. We can think
of this as "horizontal" composition: using multiple resources at once.
We'll often also need "vertical" composition: implementing one resource
in terms of one or more other resources.

We'll see an example of this in this section. First, we'll implement a
small API for graphics, in an interface ``Draw``, supporting:

* Opening a window, creating a double-buffered surface to draw on
* Drawing lines and rectangles onto a surface
* "Flipping" buffers, displaying the surface we've just drawn onto in
  the window
* Closing a window

Then, we'll use this API to implement a higher level API for turtle graphics,
in an ``interface``.
This will require not only the ``Draw`` interface, but also a representation
of the turtle state (location, direction and pen colour).

.. topic:: SDL bindings

    For the examples in this section, you'll need to install the
    (very basic!) SDL bindings for Idris, available from
    https://github.com/edwinb/SDL-idris. These bindings implement a small
    subset of the SDL API, and are for illustrative purposes only.
    Nevertheless, they are enough to implement small graphical programs
    and demonstrate the concepts of this section.

    Once you've installed this package, you can start Idris with the
    ``-p sdl`` flag, for the SDL bindings, and the ``-p contrib`` flag,
    for the ``Control.ST`` library.

The ``Draw`` interface
----------------------

We're going to use the Idris SDL bindings for this API, so you'll need
to import ``Graphics.SDL`` once you've installed the bindings.
We'll start by defining the ``Draw`` interface, which includes a data type
representing a surface on which we'll draw lines and rectangles:

.. code-block:: idris

    interface Draw (m : Type -> Type) where 
        Surface : Type

We'll need to be able to create a new ``Surface`` by opening a window:

.. code-block:: idris

    initWindow : Int -> Int -> ST m Var [add Surface]

However, this isn't quite right. It's possible that opening a window
will fail, for example if our program is running in a termina without
a windowing system available. So, somehow, ``initWindow`` needs to cope
with the possibility of failure. We can do this by returning a
``Maybe Var``, rather than a ``Var``, and only adding the ``Surface``
on success:

.. code-block:: idris

    initWindow : Int -> Int -> ST m (Maybe Var) [addIfJust Surface]

This uses a type level function ``addIfJust``, defined in ``Control.ST``
which returns an ``Action`` that only adds a resource if the operation
succeeds (that is, returns a result of the form ``Just val``.

.. topic:: ``addIfJust`` and ``addIfRight``

  ``Control.ST`` defines functions for constructing new resources if an
  operation succeeds. As well as ``addIfJust``, which adds a resource if
  an operation returns ``Just ty``, there's also ``addIfRight``:

  .. code-block:: idris
     
     addIfJust : Type -> Action (Maybe Var)
     addIfRight : Type -> Action (Either a Var)

  Each of these is implemented in terms of the following primitive action
  ``Add``, which takes a function to construct a resource list from the result
  of an operation:

  .. code-block:: idris
  
     Add : (ty -> Resources) -> Action ty
  
  Using this, you can create your own actions to add resources 
  based on the result of an operation, if required. For example,
  ``addIfJust`` is implemented as follows:

  .. code-block:: idris

     addIfJust : Type -> Action (Maybe Var)
     addIfJust ty = Add (maybe [] (\var => [var ::: ty]))

If we create windows, we'll also need to be able to delete them:

.. code-block:: idris

    closeWindow : (win : Var) -> ST m () [remove win Surface]

We'll also need to respond to events such as keypresses and mouse clicks.
The ``Graphics.SDL`` library provides an ``Event`` type for this, and
we can ``poll`` for events which returns the last event which occurred,
if any:

.. code-block:: idris

    poll : ST m (Maybe Event) []

The remaining methods of ``Draw`` are ``flip``, which flips the buffers
displaying everything that we've drawn since the previous ``flip``, and
two methods for drawing: ``filledRectangle`` and ``drawLine``.

.. code-block:: idris

    flip : (win : Var) -> ST m () [win ::: Surface]
    filledRectangle : (win : Var) -> (Int, Int) -> (Int, Int) -> Col -> ST m () [win ::: Surface]
    drawLine : (win : Var) -> (Int, Int) -> (Int, Int) -> Col -> ST m () [win ::: Surface]

We define colours as follows, as four components (red, green, blue, alpha):

.. code-block:: idris

  data Col = MkCol Int Int Int Int

  black : Col
  black = MkCol 0 0 0 255

  red : Col
  red = MkCol 255 0 0 255

  green : Col
  green = MkCol 0 255 0 255

  -- Also blue, yellow, magenta, cyan, white, similarly...

If you import ``Graphics.SDL``, you can implement the ``Draw`` interface
using the SDL bindings as follows:

.. code-block:: idris

  interface Draw IO where
    Surface = State SDLSurface

    initWindow x y = do Just srf <- lift (startSDL x y)
                             | pure Nothing
                        var <- new srf
                        pure (Just var)

    closeWindow win = do lift endSDL
                         delete win

    flip win = do srf <- read win
                  lift (flipBuffers srf)
    poll = lift pollEvent

    filledRectangle win (x, y) (ex, ey) (MkCol r g b a)
         = do srf <- read win
              lift $ filledRect srf x y ex ey r g b a
    drawLine win (x, y) (ex, ey) (MkCol r g b a)
         = do srf <- read win
              lift $ drawLine srf x y ex ey r g b a

In this implementation, we've used ``startSDL`` to initialise a window, which,
returns ``Nothing`` if it fails. Since the type of ``initWindow`` states that
it adds a resource when it returns a value of the form ``Just val``, we
add the surface returned by ``startSDL`` on success, and nothing on
failure.  We can only successfully initialise if ``startDSL`` succeeds.

Now that we have an implementation of ``Draw``, we can try writing some
functions for drawing into a window and execute them via the SDL bindings.
For example, assuming we have a surface ``win`` to draw onto, we can write a
``render`` function as follows which draws a line onto a black background:

.. code-block:: idris

  render : Draw m => (win : Var) -> ST m () [win ::: Surface {m}]
  render win = do filledRectangle win (0,0) (640,480) black
                  drawLine win (100,100) (200,200) red
                  flip win

The ``flip win`` at the end is necessary because the drawing primitives
are double buffered, to prevent flicker. We draw onto one buffer, off-screen,
and display the other.  When we call ``flip``, it displays the off-screen 
buffer, and creates a new off-screen buffer for drawing the next frame.

To include this in a program, we'll write a main loop which renders our
image and waits for an event to indicate the user wants to close the
application:

.. code-block:: idris

  loop : Draw m => (win : Var) -> ST m () [win ::: Surface {m}]
  loop win = do render win
                Just AppQuit <- poll
                     | _ => loop win
                pure ()

Finally, we can create a main program which initialises a window, if
possible, then runs the main loop:
                
.. code-block:: idris

  drawMain : (ConsoleIO m, Draw m) => ST m () []
  drawMain = do Just win <- initWindow 640 480
                   | Nothing => putStrLn "Can't open window"
                loop win
                closeWindow win

We can try this at the REPL using ``run``:

.. code::

  *Draw> :exec run drawMain

A higher level interface: ``TurtleGraphics``
--------------------------------------------

Turtle graphics involves a "turtle" moving around the screen, drawing a line as
it moves with a "pen". A turtle has attributes describing its location, the
direction it's facing, and the current pen colour. There are commands for
moving the turtle forwards, turning through an angle, and changing the
pen colour, among other things. One possible interface would be the
following:

.. code-block:: idris

  interface TurtleGraphics (m : Type -> Type) where
    Turtle : Type

    start : Int -> Int -> ST m (Maybe Var) [addIfJust Turtle]
    end : (t : Var) -> ST m () [Remove t Turtle]

    fd : (t : Var) -> Int -> ST m () [t ::: Turtle]
    rt : (t : Var) -> Int -> ST m () [t ::: Turtle]

    penup : (t : Var) -> ST m () [t ::: Turtle]
    pendown : (t : Var) -> ST m () [t ::: Turtle]
    col : (t : Var) -> Col -> ST m () [t ::: Turtle]

    render : (t : Var) -> ST m () [t ::: Turtle]

Like ``Draw``, we have a command for initialising the turtle (here called
``start``) which might fail if it can't create a surface for the turtle to
draw on. There is also a ``render`` method, which is intended to render the
picture drawn so far in a window.  One possible program with this interface
is the following, with draws a colourful square:

.. code-block:: idris

  turtle : (ConsoleIO m, TurtleGraphics m) => ST m () []
  turtle = with ST do
              Just t <- start 640 480
                   | Nothing => putStr "Can't make turtle\n"
              col t yellow
              fd t 100; rt t 90
              col t green
              fd t 100; rt t 90
              col t red
              fd t 100; rt t 90
              col t blue
              fd t 100; rt t 90
              render t
              end t

.. topic:: ``with ST do``

  The purpose of ``with ST do`` in ``turtle`` is to disambiguate ``(>>=)``,
  which could be either the version from the ``Monad`` interface, or the
  version from ``ST``. Idris can work this out itself, but it takes time to
  try all of the possibilities, so the ``with`` clause can
  speed up type checking.

To implement the interface, we could try using ``Surface`` to represent
the surface for the turtle to draw on:

.. code-block:: idris

    implementation Draw m => TurtleGraphics m where
      Turtle = Surface {m}

Knowing that a ``Turtle`` is represented as a ``Surface``, we can use the
methods provided by ``Draw`` to implement the turtle.  Unfortunately, though,
this isn't quite enough. We need to store more information: in particular, the
turtle has several attributes which we need to store somewhere.
So, not only do we need to represent the turtle as a ``Surface``, we need
to store some additional state. We can achieve this using a *composite*
resource.

Introducing composite resources
-------------------------------

A *composite* resource is built up from a list of other resources, and
is implemented using the following type, defined by ``Control.ST``:

.. code-block:: idris

  data Composite : List Type -> Type 

If we have a composite resource, we can split it into its constituent
resources, and create new variables for each of those resources, using
the *split* function. For example:

.. code-block:: idris

  splitComp : (comp : Var) -> ST m () [comp ::: Composite [State Int, State String]]
  splitComp comp = do [int, str] <- split comp
                      ?whatNow
 
The call ``split comp`` extracts the ``State Int`` and ``State String`` from
the composite resource ``comp``, and stores them in the variables ``int``
and ``str`` respectively. If we check the type of ``whatNow``, we'll see
how this has affected the resource list:

.. code-block:: idris

      int : Var
      str : Var
      comp : Var
      m : Type -> Type
    --------------------------------------
    whatNow : STrans m () [int ::: State Int, str ::: State String, comp ::: State ()]
                          (\result => [comp ::: Composite [State Int, State String]])

So, we have two new resources ``int`` and ``str``, and the type of
``comp`` has been updated to the unit type, so currently holds no data.
This is to be expected: we've just extracted the data into individual
resources after all.

Now that we've extracted the individual resources, we can manipulate them
directly (say, incrementing the ``Int`` and adding a newline to the
``String``) then rebuild the composite resource using ``combine``:

.. code-block:: idris

  splitComp : (comp : Var) ->
              ST m () [comp ::: Composite [State Int, State String]]
  splitComp comp = do [int, str] <- split comp
                      update int (+ 1)
                      update str (++ "\n")
                      combine comp [int, str]
                      ?whatNow

As ever, we can check the type of ``whatNow`` to see the effect of
``combine``:

.. code-block:: idris

      comp : Var
      int : Var
      str : Var
      m : Type -> Type
    --------------------------------------
    whatNow : STrans m () [comp ::: Composite [State Int, State String]]
                     (\result => [comp ::: Composite [State Int, State String]])

The effect of ``combine``, therefore, is to take existing
resources and merge them into one composite resource. Before we run
``combine``, the target resource must exist (``comp`` here) and must be
of type ``State ()``.

It is instructive to look at the types of ``split`` and combine to see
the requirements on resource lists they work with. The type of ``split``
is the following:

.. code-block:: idris

    split : (lbl : Var) -> {auto prf : InState lbl (Composite vars) res} ->
            STrans m (VarList vars) res (\ vs => mkRes vs ++ updateRes res prf (State ()))

The implicit ``prf`` argument says that the ``lbl`` being split must be
a composite resource. It returns a variable list, built from the composite
resource, and the ``mkRes`` function makes a list of resources of the
appropriate types. Finally, ``updateRes`` updates the composite resource to
have the type ``State ()``.

The ``combine`` function does the inverse:

.. code-block:: idris

    combine : (comp : Var) -> (vs : List Var) ->
              {auto prf : InState comp (State ()) res} ->
              {auto var_prf : VarsIn (comp :: vs) res} ->
              STrans m () res (const (combineVarsIn res var_prf))

The implicit ``prf`` argument here ensures that the target resource ``comp``
has type ``State ()``. That is, we're not overwriting any other data.
The implicit ``var_prf`` argument is similar to ``SubRes`` in ``call``, and
ensures that every variable we're using to build the composite resource
really does exist in the current resource list.

We can use composite resources to implement our higher level ``TurtleGraphics``
API in terms of ``Draw``, and any additional resources we need.

Implementing ``Turtle``
-----------------------

Now that we've seen how to build a new resource from an existing collection,
we can implement ``Turtle`` using a composite resource, containing the
``Surface`` to draw on, and individual states for the pen colour and the
pen location and direction. We also have a list of lines, which describes
what we'll draw onto the ``Surface`` when we call ``render``:

.. code-block:: idris

  Turtle = Composite [Surface {m}, -- surface to draw on
                      State Col,  -- pen colour
                      State (Int, Int, Int, Bool), -- pen location/direction/d
                      State (List Line)] -- lines to draw on render

A ``Line`` is defined as a start location, and end location, and a colour:

.. code-block:: idris

  Line : Type
  Line = ((Int, Int), (Int, Int), Col)

To implement ``start``, which creates a new ``Turtle`` (or returns ``Nothing``)
if this is impossible, we begin by initialising the drawing surface then
all of the components of the state. Finally, we combine all of these
into a composite resource for the turtle:

.. code-block:: idris

    start x y = do Just srf <- initWindow x y
                        | Nothing => pure Nothing
                   col <- new white
                   pos <- new (320, 200, 0, True)
                   lines <- new []
                   turtle <- new ()
                   combine turtle [srf, col, pos, lines]
                   pure (Just turtle)

To implement ``end``, which needs to dispose of the turtle,
we deconstruct the composite resource, close the window,
then remove each individual resource. Remember that we can only ``delete``
a ``State``, so we need to ``split`` the composite resource, close the
drawing surface cleanly with ``closeWindow``, then ``delete`` the states:

.. code-block:: idris

    end t = do [srf, col, pos, lines] <- split t
               closeWindow srf; delete col; delete pos; delete lines; delete t

For the other methods, we need to ``split`` the resource to get each
component, and ``combine`` into a composite resource when we're done.
As an example, here's ``penup``:

.. code-block:: idris

    penup t = do [srf, col, pos, lines] <- split t -- Split the composite resource
                 (x, y, d, _) <- read pos          -- Deconstruct the pen position
                 write pos (x, y, d, False)        -- Set the pen down flag to False
                 combine t [srf, col, pos, lines]  -- Recombine the components

The remaining operations on the turtle follow a similar pattern. See
``samples/ST/Graphics/Turtle.idr`` in the Idris distribution for the full
details. It remains to render the image created by the turtle:

.. code-block:: idris

    render t = do [srf, col, pos, lines] <- split t -- Split the composite resource
                  filledRectangle srf (0, 0) (640, 480) black -- Draw a background
                  drawAll srf !(read lines)         -- Render the lines drawn by the turtle
                  flip srf                          -- Flip the buffers to display the image
                  combine t [srf, col, pos, lines]
                  Just ev <- poll
                    | Nothing => render t           -- Keep going until a key is pressed
                  case ev of
                       KeyUp _ => pure ()           -- Key pressed, so quit
                       _ => render t
     where drawAll : (srf : Var) -> List Line -> ST m () [srf ::: Surface {m}]
           drawAll srf [] = pure ()
           drawAll srf ((start, end, col) :: xs)
              = do drawLine srf start end col       -- Draw a line in the appropriate colour
                   drawAll srf xs
