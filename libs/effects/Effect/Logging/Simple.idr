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
    Log : (lvl : Nat)
       -> (msg : String)
       -> Logging () Nat (\v => Nat)

||| A Logging Effect.
LOG : EFFECT
LOG = MkEff Nat Logging

-- For logging in the IO context
instance Handler Logging IO where
    handle l (Log lvl msg) k = do
      case lvl <= l  of
        False   => k () l
        True  =>  do
          printLn $ unwords [show lvl, ":", msg]
          k () l

||| Log `msg` at the given level.
|||
||| @l The level to log.
||| @m The message to log.
log : (l : Nat) -> (m : String) -> Eff () [LOG]
log lvl msg = call $ Log lvl msg

-- --------------------------------------------------------------------- [ EOF ]
