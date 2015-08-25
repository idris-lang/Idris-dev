-- -------------------------------------------------------------- [ Simple.idr ]
-- Module    : Logging.idr
-- Copyright : (c) The Idris Community
-- License   : see LICENSE
--------------------------------------------------------------------- [ EOH ]

||| A simple logging effect that allows messages to be logged at
||| different numerical level. The higher the number the grater in
||| verbosity the logging.
|||
||| In this effect the resource we are computing over is the logging
||| level itself.
|||
module Effect.Logging.Simple

import Effects
import public Effect.Logging.Level

import Control.IOExcept -- TODO Add IO Logging Handler

||| A Logging effect that displays a logging message to be logged at a
||| certain level.
data Logging : Effect where
    SetLvl : (lvl : Nat)
          -> sig Logging () Nat Nat
    Log : (lvl : Nat)
       -> (msg : String)
       -> sig Logging () Nat

||| A Logging Effect.
LOG : EFFECT
LOG = MkEff Nat Logging

-- For logging in the IO context
instance Handler Logging IO where
    handle st (SetLvl newL) k = k () st
    handle st (Log lvl msg) k = do
      case lvl <= st  of
        False => k () st
        True  =>  do
          printLn $ unwords [show lvl, ":", msg]
          k () st

||| Set the logging level.
|||
||| @l The new logging level.
setLogLvl : (l : Nat) -> Eff () [LOG]
setLogLvl l = call $ SetLvl l

||| Log `msg` at the given level.
|||
||| @l The level to log.
||| @m The message to log.
log : (l : Nat) -> (m : String) -> Eff () [LOG]
log lvl msg = call $ Log lvl msg

-- --------------------------------------------------------------------- [ EOF ]
