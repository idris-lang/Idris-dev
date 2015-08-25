-- ------------------------------------------------------------- [ Logging.idr ]
-- Module    : Logging.idr
-- Copyright : (c) The Idris Community
-- License   : see LICENSE
-- --------------------------------------------------------------------- [ EOH ]

||| A logging effect that allows messages to be logged using both
||| numerical levels and user specified categories. The higher the
||| logging level the grater in verbosity the logging.
|||
||| In this effect the resource we are computing over is the logging
||| level itself and the list of categories to show.
|||
module Effect.Logging

import Effects
import public Effect.Logging.Level

%access public

record LogRes (a : Type) where
  constructor MkLogRes
  lvl  : Nat
  cats : List a

instance (Show a) => Show (LogRes a) where
  show (MkLogRes l cs) = unwords ["Log Settings:", show l, show cs]

instance (Eq a) => Eq (LogRes a) where
  (==) (MkLogRes x y) (MkLogRes x' y') = x' == x && y == y'

instance Default (LogRes a) where
  default = MkLogRes Z Nil

||| A Logging effect to log levels and categories.
data Logging : Effect where
    ||| Log a message.
    |||
    ||| @lvl  The logging level it should appear at.
    ||| @cats The categories it should appear under.
    ||| @msg  The message to log.
    Log : (Show a, Eq a) =>
          (lvl : Nat)
       -> (cats : List a)
       -> (msg : String)
       -> sig Logging () (LogRes a)

    ||| Change the logging level.
    |||
    ||| @nlvl The new logging level
    SetLogLvl : (Show a, Eq a) =>
                (nlvl : Nat) ->
                sig Logging () (LogRes a) (LogRes a)

    ||| Change the categories to show.
    |||
    ||| @ncats The new categories.
    SetLogCats : (Show a, Eq a) =>
                 (ncats : List a) ->
                 sig Logging () (LogRes a) (LogRes a)

    ||| Initialise the logging.
    |||
    ||| @nlvl  The new logging level.
    ||| @ncats The categories to show.
    InitLogger : (Show a, Eq a) =>
                 (nlvl  : Nat) ->
                 (ncats : List a) ->
                 sig Logging () (LogRes a) (LogRes a)

instance Handler Logging IO where
    handle st (SetLogLvl  nlvl)  k = do
        let newSt = record {lvl = nlvl}  st
        k () newSt
    handle st (SetLogCats newcs) k = do
        let newSt = record {cats = newcs} st
        k () newSt

    handle st  (InitLogger l cs) k = do
        let newSt = MkLogRes l cs
        k () newSt

    handle st (Log l cs' msg) k = do
      case l <= lvl st of
        False => k () st
        True  =>  do
          let res = and $ map (\x => elem x cs') (cats st)
          let prompt = if isNil (cats st)
                         then unwords [show l, ":"]
                         else unwords [show l, ":", show (cats st)]
          if res || isNil (cats st)
            then do
              printLn $ unwords [prompt, msg]
              k () st
            else k () st

||| The Logging effect.
|||
||| @cTy The type used to differentiate categories.
LOG : (cTy : Type) -> EFFECT
LOG cTy = MkEff (LogRes cTy) Logging

||| Change the logging level.
|||
||| @l  The new logging level.
setLoglvl : (Eq a, Show a) => (l : Nat) -> Eff () [LOG a]
setLoglvl l = call $ SetLogLvl l

||| Change the categories to show.
|||
||| @cs The new categories.
setLogCats : (Show a, Eq a) => (cs : List a) -> Eff () [LOG a]
setLogCats cs = call $ SetLogCats cs

||| Initialise the Logger.
|||
||| @l  The logging level.
||| @cs The categories to show.
initLogger : (Eq a, Show a) => (l : Nat)
                            -> (cs : List a)
                            -> Eff () [LOG a]
initLogger l cs = call $ InitLogger l cs

||| Log the given message at the given level and assign it the list of categories.
|||
||| @l The logging level.
||| @cs The logging categories.
||| @m THe message to be logged.
log : (Show a, Eq a) => (l : Nat)
    -> (cs : List a) -> (m : String) -> Eff () [LOG a]
log l cs msg = call $ Log l cs msg

-- --------------------------------------------------------------------- [ EOF ]
