.. _elaborator-reflection:

*********************
Elaborator Reflection
*********************

The Idris elaborator is responsible for converting high-level Idris code into the core language.
It is implemented as a kind of embedded tactic language in Haskell, where tactic scripts are written in an *elaboration monad* that provides error handling and a proof state.
For details, see Edwin Brady's 2013 paper in the Journal of Functional Programming.

Elaborator reflection makes the elaboration type as well as a selection of its tactics available to Idris code.
This means that metaprograms written in Idris can have complete control over the elaboration process, generating arbitrary code, and they have access to all of the facilities available in the elaborator, such as higher-order unification, type checking, and emitting auxiliary definitions.

The Elaborator State
====================

The elaborator state contains information about the ongoing elaboration process.
In particular, it contains a *goal type*, which is to be filled by an under-construction *proof term*.
The proof term can contain *holes*, each of which has a scope in which it is valid and a type.
Some holes may additionally contain *guesses*, which can be substituted in the scope of the hole.
The holes are tracked in a *hole queue*, and one of them is *focused*.
In addition to the goal type, proof term, and holes, the elaborator state contains a collection of unsolved unification problems that can affect elaboration.

The elaborator state is not directly available to Idris programs.
Instead, it is modified through the use of *tactics*, which are operations that affect the elaborator state.
A tactic that returns a value of type ``a``, potentially modifying the elaborator state, has type ``Elab a``.
The default tactics are all in the namespace ``Language.Reflection.Elab.Tactics``.


Running Elaborator Scripts
==========================

On their own, tactics have no effect.
The meta-operation ``%runElab script`` runs ``script`` in the current elaboration context.
For example, the following script constructs the identity function at type ``Nat``:

.. code-block:: idris

    idNat : Nat -> Nat
    idNat = %runElab (do intro `{{x}}
                         fill (Var `{{x}})
                         solve)


On the right-hand side, the Idris elaborator has the goal ``Nat -> Nat``.
When it encounters the ``%runElab`` directive, it fulfills this goal by running the provided script.
The first tactic, ``intro``, constructs a lambda that binds the name ``x``.
The name argument is optional because a default name can be taken from the function type.
Now, the proof term is of the form ``\x : Nat => {hole}``.
The second tactic, ``fill``, fills this hole with a guess, giving the term ``\x : Nat => {hole≈x}``.
Finally, the ``solve`` tactic instantiates the guess, giving the result ``\x : Nat => x``.

Because elaborator scripts are ordinary Idris expressions, it is also possible to use them in multiple contexts.
Note that there is nothing ``Nat``-specific about the above script.
We can generate identity functions at any concrete type using the same script:

.. code-block:: idris

    mkId : Elab ()
    mkId = do intro `{{x}}
              fill (Var `{{x}})
              solve

    idNat : Nat -> Nat
    idNat = %runElab mkId

    idUnit : () -> ()
    idUnit = %runElab mkId

    idString : String -> String
    idString = %runElab mkId


Interactively Building Elab Scripts
===================================

You can build an ``Elab`` script interactively at the REPL.
Use the command ``:metavars``, or ``:m`` for short, to list the available holes.
Then, issue the ``:elab <hole>`` command at the REPL
to enter the elaboration shell.

At the shell, you can enter proof tactics to alter the proof state.
You can view the system-provided tactics prior to entering the shell
by issuing the REPL command ``:browse Language.Reflection.Elab.Tactics``.
When you have discharged all goals, you can complete the proof
using the ``:qed`` command and receive in return an elaboration script
that fills the hole.

The interactive elaboration shell accepts a limited number of commands,
including a subset of the commands understood by the normal Idris REPL
as well as some elaboration-specific commands.

General-purpose commands:

- ``:eval <EXPR>``, or ``:e <EXPR>`` for short, evaluates the provided expression
  and prints the result.

- ``:type <EXPR>``, or ``:t <EXPR>`` for short, prints the provided expression
  together with its type.

- ``:search <TYPE>`` searches for definitions having the provided type.

- ``:doc <NAME>`` searches for definitions with the provided name and prints their
  documentation.


Commands for viewing the proof state:

- ``:state`` displays the current state of the term being constructed. It lists both
  other goals and the current goal.

- ``:term`` displays the current proof term as well as its yet-to-be-filled holes.


Commands for manipulating the proof state:

- ``:undo`` undoes the effects of the last tactic.

- ``:abandon`` gives up on proving the current lemma and quits the elaboration shell.

- ``:qed`` finishes the script and exits the elaboration shell. The shell will only accept
  this command once it reports, "No more goals." On exit, it will print out the finished
  elaboration script for you to copy into your program.


Failure
=======

Some tactics may *fail*.
For example, ``intro`` will fail if the focused hole does not have a function type, ``solve`` will fail if the current hole does not contain a guess, and ``fill`` will fail if the term to be filled in has the wrong type.
Scripts can also fail explicitly using the ``fail`` tactic.

To account for failure, there is an ``Alternative`` implementation for ``Elab``.
The ``<|>`` operator first tries the script to its left.
If that script fails, any changes that it made to the state are undone and the right argument is executed.
If the first argument succeeds, then the second argument is not executed.

Querying the Elaboration State
==============================

``Elab`` includes operations to query the elaboration state, allowing scripts to use information about their environment to steer the elaboration process.
The ordinary Idris bind syntax can be used to propagate this information.
For example, a tactic that solves the current goal when it is the unit type might look like this:

.. code-block:: idris

    triv : Elab ()
    triv = do compute
              g <- getGoal
              case (snd g) of
                `(() : Type) => do fill `(() : ())
                                   solve
                otherGoal => fail [ TermPart otherGoal
                                  , TextPart "is not trivial"
                                  ]


The tactic ``compute`` normalises the type of its goal with respect to the current context.
While not strictly necessary, this allows ``triv`` to be used in contexts where the triviality of the goal is not immediately apparent.
Then, ``getGoal`` is used, and its result is bound to ``g``.
Because it returns a pair consisting of the current goal's name and type, we case-split on its second projection.
If the goal type turns out to have been the unit type, we fill using the unit constructor and solve the goal.
Otherwise, we fail with an error message informing the user that the current goal is not trivial.

Additionally, the elaboration state can be dumped into an error message with the ``debug`` tactic.
A variant, ``debugMessage``, allows arbitrary messages to be included with the state, allowing for a kind of "``printf`` debugging" of elaboration scripts.
The message format used by ``debugMessage`` is the same for errors produced by the error reflection mechanism, allowing the re-use of the Idris pretty-printer when rendering messages.

Changing the Global Context
===========================

``Elab`` scripts can modify the global context during execution.
Just as the Idris elaborator produces auxiliary definitions to implement features such as ``where``-blocks and ``case`` expressions, user elaboration scripts may need to define functions.
Furthermore, this allows ``Elab`` reflection to be used to implement features such as interface deriving.
The operations ``declareType``, ``defineFunction``, and ``addImplementation`` allow ``Elab`` scripts to modify the global context.

Using Idris's Features
======================

The Idris compiler has a number of ways to automate the construction of terms.
On its own, the ``Elab`` state and its interactions with the unifier allow implicits to be solved using unification.
Additional operations use further features of Idris.
In particular, ``resolveTC`` solves the current goal using interface resolution, ``search`` invokes the proof search mechanism, and ``sourceLocation`` finds the context in the original file at which the elaboration script is invoked.


Recursive Elaboration
=====================

The elaboration mechanism can be invoked recursively using the ``runElab`` tactic.
This tactic takes a goal type and an elaboration script as arguments and runs the script in a fresh lexical environment to create an inhabitant of the provided goal type.
This is primarily useful for code generation, particularly for generating pattern-matching clauses, where variable scope needs to be one that isn't the present local context.

Learn More
==========
While this documentation is still incomplete, elaboration reflection works in Idris today.
As you wait for the completion of the documentation, the list of built-in tactics can be obtained using the ``:browse`` command in an Idris REPL or the corresponding feature in one of the graphical IDE clients to explore the ``Language.Reflection.Elab.Tactics`` namespace.
All of the built-in tactics contain documentation strings.
