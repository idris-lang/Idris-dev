.. _sect-appendix:

***************
Effects Summary
***************

This appendix gives interfaces for the core effects provided by the
library.

EXCEPTION
=========

.. code-block:: idris

    module Effect.Exception

    import Effects
    import System
    import Control.IOExcept

    EXCEPTION : Type -> EFFECT

    raise : a -> Eff b [EXCEPTION a]

    Handler (Exception a) Maybe where { ... }
    Handler (Exception a) List where { ... }
    Handler (Exception a) (Either a) where { ... }
    Handler (Exception a) (IOExcept a) where { ... }
    Show a => Handler (Exception a) IO where { ... }

FILE\_IO
========

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

    readLine  :           Eff String [FILE_IO (OpenFile Read)]
    writeLine : String -> Eff () [FILE_IO (OpenFile Write)]
    eof       :           Eff Bool [FILE_IO (OpenFile Read)]

    Handler FileIO IO where { ... }

RND
===

.. code-block:: idris

    module Effect.Random

    import Effects
    import Data.Vect
    import Data.Fin

    RND : EFFECT

    srand  : Integer ->            Eff () [RND]
    rndInt : Integer -> Integer -> Eff Integer [RND]
    rndFin : (k : Nat) ->          Eff (Fin (S k)) [RND]

    Handler Random m where { ... }

SELECT
======

.. code-block:: idris

    module Effect.Select

    import Effects

    SELECT : EFFECT

    select : List a -> Eff a [SELECT]

    Handler Selection Maybe where { ... }
    Handler Selection List where { ... }

STATE
=====

.. code-block:: idris

    module Effect.State

    import Effects

    STATE : Type -> EFFECT

    get    :             Eff x [STATE x]
    put    : x ->        Eff () [STATE x]
    putM   : y ->        Eff () [STATE x] [STATE y]
    update : (x -> x) -> Eff () [STATE x]

    Handler State m where { ... }

STDIO
=====

.. code-block:: idris

    module Effect.StdIO

    import Effects
    import Control.IOExcept

    STDIO : EFFECT

    putChar  : Char   -> Eff () [STDIO]
    putStr   : String -> Eff () [STDIO]
    putStrLn : String -> Eff () [STDIO]

    getStr   :           Eff String [STDIO]
    getChar  :           Eff Char [STDIO]

    Handler StdIO IO where { ... }
    Handler StdIO (IOExcept a) where { ... }

SYSTEM
======

.. code-block:: idris

    module Effect.System

    import Effects
    import System
    import Control.IOExcept

    SYSTEM : EFFECT

    getArgs :           Eff (List String) [SYSTEM]
    time    :           Eff Int [SYSTEM]
    getEnv  : String -> Eff (Maybe String) [SYSTEM]

    Handler System IO where { ... }
    Handler System (IOExcept a) where { ... }
