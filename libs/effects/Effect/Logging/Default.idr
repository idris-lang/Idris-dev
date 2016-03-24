-- ------------------------------------------------------------- [ Default.idr ]
-- Module    : Default.idr
-- Copyright : (c) The Idris Community
-- License   : see LICENSE
--------------------------------------------------------------------- [ EOH ]
||| The default logging effect that allows messages to be logged at
||| different numerical levels. The higher the number the greater in
||| verbosity the logging.
|||
||| In this effect the resource we are computing over is the logging
||| level itself.
|||
module Effect.Logging.Default

import Effects
import public Effect.Logging.Level

%access public export

-- ------------------------------------------------------------ [ The Resource ]

||| The resource that the log effect is defined over.
record LogRes where
  constructor MkLogRes
  getLevel : LogLevel n

implementation Default LogRes where
  default = MkLogRes OFF

-- ------------------------------------------------------ [ The Logging Effect ]

||| A Logging effect that displays a logging message to be logged at a
||| certain level.
data Logging : Effect where
    ||| Change the logging level.
    |||
    ||| @lvl The new logging level.
    SetLvl : (lvl : LogLevel n)
          -> sig Logging () (LogRes) (LogRes)

    ||| Log a message.
    |||
    ||| @lvl  The logging level it should appear at.
    ||| @msg  The message to log.
    Log : (lvl : LogLevel n)
       -> (msg : String)
       -> sig Logging () (LogRes)

-- -------------------------------------------------------------- [ IO Handler ]

-- For logging in the IO context
implementation Handler Logging IO where
    handle st (SetLvl newLvl) k = k () (MkLogRes newLvl)
    handle st (Log lvl msg) k = do
      case cmpLevel lvl (getLevel st)  of
        GT        => k () st
        otherwise =>  do
          putStrLn $ unwords [show lvl, ":", msg]
          k () st

-- ------------------------------------------------------- [ Effect Descriptor ]

||| A Logging Effect.
LOG : EFFECT
LOG = MkEff (LogRes) Logging

-- ----------------------------------------------------------- [ Effectful API ]

||| Set the logging level.
|||
||| @l The new logging level.
setLogLvl : (l : LogLevel n) -> Eff () [LOG]
setLogLvl l = call $ SetLvl l

||| Log `msg` at the given level specified as a natural number.
|||
||| @l The level to log.
||| @m The message to log.
log : (l : LogLevel n) -> (m : String) -> Eff () [LOG]
log l msg = call $ Log l msg

||| Log `msg` at the given level specified as a natural number.
|||
||| @l The level to log.
||| @m The message to log.
logN : (l : Nat) -> {auto prf : LTE l 70} -> (m : String) -> Eff () [LOG]
logN l msg = call $ Log (snd lvl) msg
  where
    lvl : (n ** LogLevel n)
    lvl = case cast {to=String} (cast {to=Int} l) of
            "0"  => (_ ** OFF)
            "10" => (_ ** TRACE)
            "20" => (_ ** DEBUG)
            "30" => (_ ** INFO)
            "40" => (_ ** WARN)
            "50" => (_ ** FATAL)
            "60" => (_ ** ERROR)
            _    => (_ ** CUSTOM l)

trace :  String -> Eff () [LOG]
trace msg = call $ Log TRACE msg

debug :  String -> Eff () [LOG]
debug msg = call $ Log DEBUG msg

info :  String -> Eff () [LOG]
info msg = call $ Log INFO msg

warn :  String -> Eff () [LOG]
warn msg = call $ Log WARN msg

fatal :  String -> Eff () [LOG]
fatal msg = call $ Log FATAL msg

error :  String -> Eff () [LOG]
error msg = call $ Log ERROR msg

-- --------------------------------------------------------------------- [ EOF ]
