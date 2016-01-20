.. _sect-hangman:

***************************************
Example: A “Mystery Word” Guessing Game
***************************************

In this section, we will use the techniques and specific effects
discussed in the tutorial so far to implement a larger example, a simple
text-based word-guessing game. In the game, the computer chooses a word,
which the player must guess letter by letter. After a limited number of
wrong guesses, the player loses [1]_.

We will implement the game by following these steps:

#. Define the game state, in enough detail to express the rules

#. Define the rules of the game (i.e. what actions the player may take,
   and how these actions affect the game state)

#. Implement the rules of the game (i.e. implement state updates for
   each action)

#. Implement a user interface which allows a player to direct actions

Step 2 may be achieved by defining an effect which depends on the state
defined in step 1. Then step 3 involves implementing a ``Handler`` for
this effect. Finally, step 4 involves implementing a program in ``Eff``
using the newly defined effect (and any others required to implement the
interface).

Step 1: Game State
==================

First, we categorise the game states as running games (where there are a
number of guesses available, and a number of letters still to guess), or
non-running games (i.e. games which have not been started, or games
which have been won or lost).

.. code-block:: idris

    data GState = Running Nat Nat | NotRunning

Notice that at this stage, we say nothing about what it means to make a
guess, what the word to be guessed is, how to guess letters, or any
other implementation detail. We are only interested in what is necessary
to describe the game rules.

We will, however, parameterise a concrete game state ``Mystery`` over
this data:

.. code-block:: idris

    data Mystery : GState -> Type

Step 2: Game Rules
==================

We describe the game rules as a dependent effect, where each action has
a *precondition* (i.e. what the game state must be before carrying out
the action) and a *postcondition* (i.e. how the action affects the game
state). Informally, these actions with the pre- and postconditions are:

Guess
    Guess a letter in the word.

    -  Precondition: The game must be running, and there must be both
       guesses still available, and letters still to be guessed.

    -  Postcondition: If the guessed letter is in the word and not yet
       guessed, reduce the number of letters, otherwise reduce the
       number of guesses.

Won
    Declare victory

    -  Precondition: The game must be running, and there must be no
       letters still to be guessed.

    -  Postcondition: The game is no longer running.

Lost
    Accept defeat

    -  Precondition: The game must be running, and there must be no
       guesses left.

    -  Postcondition: The game is no longer running.

NewWord
    Set a new word to be guessed

    -  Precondition: The game must not be running.

    -  Postcondition: The game is running, with 6 guesses available (the
       choice of 6 is somewhat arbitrary here) and the number of unique
       letters in the word still to be guessed.

Get
    Get a string representation of the game state. This is for display
    purposes; there are no pre- or postconditions.

We can make these rules precise by declaring them more formally in an
effect signature:

.. code-block:: idris

    data MysteryRules : Effect where
         Guess : (x : Char) ->
                 sig MysteryRules Bool
                     (Mystery (Running (S g) (S w)))
                     (\inword => if inword
                                 then Mystery (Running (S g) w)
                                 else Mystery (Running g (S w)))
         Won  : sig MysteryRules () (Mystery (Running g 0))
                                    (Mystery NotRunning)
         Lost : sig MysteryRules () (Mystery (Running 0 g))
                                    (Mystery NotRunning)
         NewWord : (w : String) -> 
                   sig MysteryRules () (Mystery NotRunning) (Mystery (Running 6 (length (letters w))))
         Get : sig MysteryRules String (Mystery h)

This description says nothing about how the rules are implemented. In
particular, it does not specify *how* to tell whether a guessed letter
was in a word, just that the result of ``Guess`` depends on it.

Nevertheless, we can still create an ``EFFECT`` from this, and use it in
an ``Eff`` program. Implementing a ``Handler`` for ``MysteryRules`` will
then allow us to play the game.

.. code-block:: idris

    MYSTERY : GState -> EFFECT
    MYSTERY h = MkEff (Mystery h) MysteryRules

Step 3: Implement Rules
=======================

To *implement* the rules, we begin by giving a concrete definition of
game state:

.. code-block:: idris

    data Mystery : GState -> Type where
         Init     : Mystery NotRunning
         GameWon  : (word : String) -> Mystery NotRunning
         GameLost : (word : String) -> Mystery NotRunning
         MkG      : (word : String) ->
                    (guesses : Nat) ->
                    (got : List Char) ->
                    (missing : Vect m Char) ->
                    Mystery (Running guesses m)

If a game is ``NotRunning``, that is either because it has not yet
started (``Init``) or because it is won or lost (``GameWon`` and
``GameLost``, each of which carry the word so that showing the game
state will reveal the word to the player). Finally, ``MkG`` captures a
running game’s state, including the target word, the letters
successfully guessed, and the missing letters. Using a ``Vect`` for the
missing letters is convenient since its length is used in the type.

To initialise the state, we implement the following functions:
``letters``, which returns a list of unique letters in a ``String``
(ignoring spaces) and ``initState`` which sets up an initial state
considered valid as a postcondition for ``NewWord``.

.. code-block:: idris

    letters : String -> List Char
    initState : (x : String) -> Mystery (Running 6 (length (letters x)))

When checking if a guess is in the vector of missing letters, it is
convenient to return a *proof* that the guess is in the vector, using
``isElem`` below, rather than merely a ``Bool``:

.. code-block:: idris

    data IsElem : a -> Vect n a -> Type where
         First : IsElem x (x :: xs)
         Later : IsElem x xs -> IsElem x (y :: xs)

    isElem : DecEq a => (x : a) -> (xs : Vect n a) -> Maybe (IsElem x xs)

The reason for returning a proof is that we can use it to remove an
element from the correct position in a vector:

.. code-block:: idris

    shrink : (xs : Vect (S n) a) -> IsElem x xs -> Vect n a

We leave the definitions of ``letters``, ``init``, ``isElem`` and
``shrink`` as exercises. Having implemented these, the ``Handler``
implementation for ``MysteryRules`` is surprisingly straightforward:

.. code-block:: idris

    Handler MysteryRules m where
        handle (MkG w g got []) Won k = k () (GameWon w)
        handle (MkG w Z got m) Lost k = k () (GameLost w)

        handle st Get k = k (show st) st
        handle st (NewWord w) k = k () (initState w)

        handle (MkG w (S g) got m) (Guess x) k =
            case isElem x m of
                 Nothing => k False (MkG w _ got m)
                 (Just p) => k True (MkG w _ (x :: got) (shrink m p))

Each case simply involves directly updating the game state in a way
which is consistent with the declared rules. In particular, in
``Guess``, if the handler claims that the guessed letter is in the word
(by passing ``True`` to ``k``), there is no way to update the state in
such a way that the number of missing letters or number of guesses does
not follow the rules.

Step 4: Implement Interface
===========================

Having described the rules, and implemented state transitions which
follow those rules as an effect handler, we can now write an interface
for the game which uses the ``MYSTERY`` effect:

.. code-block:: idris

    game : Eff () [MYSTERY (Running (S g) w), STDIO]
                  [MYSTERY NotRunning, STDIO]

The type indicates that the game must start in a running state, with
some guesses available, and eventually reach a not-running state (i.e.
won or lost). The only way to achieve this is by correctly following the
stated rules.

Note that the type of ``game`` makes no assumption that there are
letters to be guessed in the given word (i.e. it is ``w`` rather than
``S w``). This is because we will be choosing a word at random from a
vector of ``String``, and at no point have we made it explicit that
those ``String`` are non-empty.

Finally, we need to initialise the game by picking a word at random from
a list of candidates, setting it as the target using ``NewWord``, then
running ``game``:

.. code-block:: idris

    runGame : Eff () [MYSTERY NotRunning, RND, SYSTEM, STDIO]
    runGame = do srand !time
                 let w = index !(rndFin _) words
                 call $ NewWord w
                 game
                 putStrLn !(call Get)

We use the system time (``time`` from the ``SYSTEM`` effect; see
Appendix :ref:`sect-appendix`) to initialise the random number
generator, then pick a random ``Fin`` to index into a list of
``words``. For example, we could initialise a word list as follows:

.. code-block:: idris

    words : ?wtype
    words = with Vect ["idris","agda","haskell","miranda",
             "java","javascript","fortran","basic",
             "coffeescript","rust"]

    wtype = proof search

.. note::
    Rather than have to explicitly declare a type with the vector’s
    length, it is convenient to give a hole ``?wtype`` and let
    Idris’s proof search mechanism find the type. This is a
    limited form of type inference, but very useful in practice.

A possible complete implementation of ``game`` is
presented below:

.. code-block:: idris

    game : Eff () [MYSTERY (Running (S g) w), STDIO]
                  [MYSTERY NotRunning, STDIO]
    game {w=Z} = Won
    game {w=S _}
         = do putStrLn !Get
              putStr "Enter guess: "
              let guess = trim !getStr
              case choose (not (guess == "")) of
                   (Left p) => processGuess (strHead' guess p)
                   (Right p) => do putStrLn "Invalid input!"
                                   game
      where
        processGuess : Char -> Eff () [MYSTERY (Running (S g) (S w)), STDIO]
                                      [MYSTERY NotRunning, STDIO]
        processGuess {g} {w} c
          = case !(Main.Guess c) of
                 True => do putStrLn "Good guess!"
                            case w of
                                 Z => Won
                                 (S k) => game
                 False => do putStrLn "No, sorry"
                             case g of
                                  Z => Lost
                                  (S k) => game

Discussion
==========

Writing the rules separately as an effect, then an implementation
which uses that effect, ensures that the implementation must follow
the rules.  This has practical applications in more serious contexts;
``MysteryRules`` for example can be though of as describing a
*protocol* that a game player most follow, or alternative a
*precisely-typed API*.

In practice, we wouldn’t really expect to write rules first then
implement the game once the rules were complete. Indeed, I didn’t do
so when constructing this example! Rather, I wrote down a set of
likely rules making any assumptions *explicit* in the state
transitions for ``MysteryRules``. Then, when implementing ``game`` at
first, any incorrect assumption was caught as a type error. The
following errors were caught during development:

- Not realising that allowing ``NewWord`` to be an arbitrary string would mean that ``game`` would have to deal with a zero-length word as a starting state.

- Forgetting to check whether a game was won before recursively calling ``processGuess``, thus accidentally continuing a finished game.

- Accidentally checking the number of missing letters, rather than the number of remaining guesses, when checking if a game was lost.

These are, of course, simple errors, but were caught by the type
checker before any testing of the game.

.. [1]
   Readers may recognise this game by the name “Hangman”.
