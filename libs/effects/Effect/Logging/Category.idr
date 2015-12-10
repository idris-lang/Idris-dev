-- ------------------------------------------------------------ [ Category.idr ]
-- Module    : Category.idr
-- Copyright : (c) The Idris Community
-- License   : see LICENSE
-- --------------------------------------------------------------------- [ EOH ]
||| A logging effect that allows messages to be logged using both
||| numerical levels and user specified categories. The higher the
||| logging level the grater in verbosity the logging.
|||
||| In this effect the resource we are computing over is the logging
||| level itself and the list of categories to show.
module Effect.Logging.Category

import Effects
import public Effect.Logging.Level

%access public export

-- -------------------------------------------------------- [ Logging Resource ]

||| The Logging details, this is the resource that the effect is
||| defined over.
record LogRes (a : Type) where
  constructor MkLogRes
  getLevel      : LogLevel n
  getCategories : List a

implementation Default (LogRes a) where
  default = MkLogRes OFF Nil

-- ------------------------------------------------------- [ Effect Definition ]

||| A Logging effect to log levels and categories.
data Logging : Effect where
    ||| Log a message.
    |||
    ||| @lvl  The logging level it should appear at.
    ||| @cats The categories it should appear under.
    ||| @msg  The message to log.
    Log : (Show a, Eq a) =>
          (lvl : LogLevel n)
       -> (cats : List a)
       -> (msg : String)
       -> sig Logging () (LogRes a)

    ||| Change the logging level.
    |||
    ||| @nlvl The new logging level
    SetLogLvl : (Show a, Eq a) =>
                (nlvl : LogLevel n) ->
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
                 (nlvl  : LogLevel n) ->
                 (ncats : List a) ->
                 sig Logging () (LogRes a) (LogRes a)

-- -------------------------------------------------------------- [ IO Handler ]

implementation Handler Logging IO where
    handle st (SetLogLvl  nlvl)  k = do
        let newSt = record {getLevel = nlvl}  st
        k () newSt
    handle st (SetLogCats newcs) k = do
        let newSt = record {getCategories = newcs} st
        k () newSt

    handle st  (InitLogger l cs) k = do
        let newSt = MkLogRes l cs
        k () newSt

    handle st (Log l cs' msg) k = do
      case cmpLevel l (getLevel st) of
        GT        => k () st
        otherwise =>  do
          let res = and $ map (\x => elem x cs') (getCategories st)
          let prompt = if isNil (getCategories st)
                         then unwords [show l, ":"]
                         else unwords [show l, ":", show (getCategories st), ":"]
          if res || isNil (getCategories st)
            then do
              putStrLn $ unwords [prompt, msg]
              k () st
            else k () st


-- ------------------------------------------------------- [ Effect Descriptor ]

||| The Logging effect.
|||
||| @a The type used to differentiate categories.
LOG : (a : Type) -> EFFECT
LOG a = MkEff (LogRes a) Logging

-- ----------------------------------------------------------- [ Effectful API ]

||| Change the logging level.
|||
||| @l  The new logging level.
setLoglvl : (Show a, Eq a) => (l : LogLevel n) -> Eff () [LOG a]
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
initLogger : (Show a, Eq a) => (l : LogLevel n)
                            -> (cs : List a)
                            -> Eff () [LOG a]
initLogger l cs = call $ InitLogger l cs

||| Log the given message at the given level indicated by a natural number and assign it the list of categories.
|||
||| @l The logging level.
||| @cs The logging categories.
||| @m THe message to be logged.
log : (Show a, Eq a) => (l : LogLevel n)
                     -> (cs : List a)
                     -> (m : String)
                     -> Eff () [LOG a]
log l cs msg = call $ Log l cs msg

||| Log the given message at the given level indicated by a natural number and assign it the list of categories.
|||
||| @l The logging level.
||| @cs The logging categories.
||| @m THe message to be logged.
logN : (Show a, Eq a) => (l : Nat)
                      -> {auto prf : LTE l 70}
                      -> (cs : List a)
                      -> (m : String)
                      -> Eff () [LOG a]
logN l cs msg = call $ Log (snd lvl) cs msg
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

trace : (Show a, Eq a) => List a -> String -> Eff () [LOG a]
trace cs msg = call $ Log TRACE cs msg

debug : (Show a, Eq a) => List a -> String -> Eff () [LOG a]
debug cs msg = call $ Log DEBUG cs msg

info : (Show a, Eq a) => List a -> String -> Eff () [LOG a]
info cs msg = call $ Log INFO cs msg

warn : (Show a, Eq a) => List a -> String -> Eff () [LOG a]
warn cs msg = call $ Log WARN cs msg

fatal : (Show a, Eq a) => List a -> String -> Eff () [LOG a]
fatal cs msg = call $ Log FATAL cs msg

error : (Show a, Eq a) => List a -> String -> Eff () [LOG a]
error cs msg = call $ Log ERROR cs msg

-- --------------------------------------------------------------------- [ EOF ]
