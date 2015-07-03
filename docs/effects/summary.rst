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

    instance           Handler (Exception a) Maybe
    instance           Handler (Exception a) List
    instance           Handler (Exception a) (Either a)
    instance           Handler (Exception a) (IOExcept a)
    instance Show a => Handler (Exception a) IO

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

    readLine  : Eff String [FILE_IO (OpenFile Read)]
    writeLine : String -> Eff () [FILE_IO (OpenFile Write)]
    eof       : Eff Bool [FILE_IO (OpenFile Read)]

    instance Handler FileIO IO

RND
===

.. code-block:: idris

    module Effect.Random

    import Effects
    import Data.Vect
    import Data.Fin

    RND : EFFECT

    srand  : Integer ->            Eff m () [RND]
    rndInt : Integer -> Integer -> Eff m Integer [RND]
    rndFin : (k : Nat) ->          Eff m (Fin (S k)) [RND]

    instance Handler Random m

SELECT
======

.. code-block:: idris

    module Effect.Select

    import Effects

    SELECT : EFFECT

    select : List a -> Eff m a [SELECT]

    instance Handler Selection Maybe
    instance Handler Selection List

STATE
=====

.. code-block:: idris

    module Effect.State

    import Effects

    STATE : Type -> EFFECT

    get    :             Eff m x [STATE x]
    put    : x ->        Eff m () [STATE x]
    putM   : y ->        Eff m () [STATE x] [STATE y]
    update : (x -> x) -> Eff m () [STATE x]

    instance Handler State m

STDIO
=====

.. code-block:: idris

    module Effect.StdIO

    import Effects
    import Control.IOExcept

    STDIO : EFFECT

    putChar  : Handler StdIO m => Char ->   Eff m () [STDIO]
    putStr   : Handler StdIO m => String -> Eff m () [STDIO]
    putStrLn : Handler StdIO m => String -> Eff m () [STDIO]

    getStr   : Handler StdIO m =>           Eff m String [STDIO]
    getChar  : Handler StdIO m =>           Eff m Char [STDIO]

    instance Handler StdIO IO
    instance Handler StdIO (IOExcept a)

SYSTEM
======

.. code-block:: idris

    module Effect.System

    import Effects
    import System
    import Control.IOExcept

    SYSTEM : EFFECT

    getArgs : Handler System e =>           Eff e (List String) [SYSTEM]
    time    : Handler System e =>           Eff e Int [SYSTEM]
    getEnv  : Handler System e => String -> Eff e (Maybe String) [SYSTEM]

    instance Handler System IO
    instance Handler System (IOExcept a)
