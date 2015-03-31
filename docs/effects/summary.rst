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

    raise : a -> { [EXCEPTION a ] } Eff m b

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

    open  : Handler FileIO e => String -> (m : Mode) ->
            { [FILE_IO ()] ==>
              {ok} [FILE_IO (if ok then OpenFile m else ())] } Eff e Bool
    close : Handler FileIO e =>
            { [FILE_IO (OpenFile m)] ==> [FILE_IO ()] } Eff e ()

    readLine  : Handler FileIO e =>
               { [FILE_IO (OpenFile Read)] } Eff e String
    writeLine : Handler FileIO e => String ->
               { [FILE_IO (OpenFile Write)] } Eff e ()
    eof       : Handler FileIO e =>
               { [FILE_IO (OpenFile Read)] } Eff e Bool

    instance Handler FileIO IO

RND
===

.. code-block:: idris

    module Effect.Random

    import Effects
    import Data.Vect
    import Data.Fin

    RND : EFFECT

    srand  : Integer ->            { [RND] } Eff m ()
    rndInt : Integer -> Integer -> { [RND] } Eff m Integer
    rndFin : (k : Nat) ->          { [RND] } Eff m (Fin (S k))

    instance Handler Random m

SELECT
======

.. code-block:: idris

    module Effect.Select

    import Effects

    SELECT : EFFECT

    select : List a -> { [SELECT] } Eff m a

    instance Handler Selection Maybe
    instance Handler Selection List

STATE
=====

.. code-block:: idris

    module Effect.State

    import Effects

    STATE : Type -> EFFECT

    get    :             { [STATE x] } Eff m x
    put    : x ->        { [STATE x] } Eff m ()
    putM   : y ->        { [STATE x] ==> [STATE y] } Eff m ()
    update : (x -> x) -> { [STATE x] } Eff m ()

    instance Handler State m

STDIO
=====

.. code-block:: idris

    module Effect.StdIO

    import Effects
    import Control.IOExcept

    STDIO : EFFECT

    putChar  : Handler StdIO m => Char ->   { [STDIO] } Eff m ()
    putStr   : Handler StdIO m => String -> { [STDIO] } Eff m ()
    putStrLn : Handler StdIO m => String -> { [STDIO] } Eff m ()

    getStr   : Handler StdIO m =>           { [STDIO] } Eff m String
    getChar  : Handler StdIO m =>           { [STDIO] } Eff m Char

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

    getArgs : Handler System e =>           { [SYSTEM] } Eff e (List String)
    time    : Handler System e =>           { [SYSTEM] } Eff e Int
    getEnv  : Handler System e => String -> { [SYSTEM] } Eff e (Maybe String)

    instance Handler System IO
    instance Handler System (IOExcept a)
