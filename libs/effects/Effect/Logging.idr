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

%access public

-- ---------------------------------------------------- [ Log Level Definition ]

||| Logging levels are natural numbers wrapped in a data type for
||| convenience.
|||
||| Several aliases have been defined to aide in semantic use of the
||| logging levels. These aliases have come from the Log4j/Python
||| family of loggers.
data LogLevel : Nat -> Type where
  ||| Log No Events
  OFF : LogLevel 0

  ||| A fine-grained debug message, typically capturing the flow through
  ||| the application.
  TRACE : LogLevel 10

  ||| A general debugging event.
  DEBUG : LogLevel 20

  |||  An event for informational purposes.
  INFO : LogLevel 30

  ||| An event that might possible lead to an error.
  WARN : LogLevel 40

  ||| An error in the application, possibly recoverable.
  ERROR : LogLevel 50

  ||| A severe error that will prevent the application from continuing.
  FATAL : LogLevel 60

  ||| All events should be logged.
  ALL : LogLevel 70

  ||| User defined logging level.
  CUSTOM : (n : Nat) -> {auto prf : LTE n 70} -> LogLevel n

instance Cast (LogLevel n) Nat where
  cast {n} _ = n

instance Show (LogLevel n) where
  show OFF        = "OFF"
  show TRACE      = "TRACE"
  show DEBUG      = "DEBUG"
  show INFO       = "INFO"
  show WARN       = "WARN"
  show FATAL      = "FATAL"
  show ERROR      = "ERROR"
  show ALL        = "ALL"
  show (CUSTOM n) = unwords ["CUSTOM", show n]

instance Eq (LogLevel n) where
  (==) x y = lvlEq x y
    where
      lvlEq : LogLevel a -> LogLevel b -> Bool
      lvlEq {a} {b} _ _ = a == b

cmpLevel : LogLevel a -> LogLevel b -> Ordering
cmpLevel {a} {b} _ _ = compare a b

||| The Logging details, this is the resource that the effect is
||| defined over.
record LogRes (a : Type) where
  constructor MkLogRes
  lvl  : LogLevel n
  cats : List a

instance (Show a) => Show (LogRes a) where
  show (MkLogRes l cs) = unwords ["Log Settings:", show l, show cs]

instance Default (LogRes a) where
  default = MkLogRes OFF Nil

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
      case cmpLevel l (lvl st) of
        GT        => k () st
        otherwise =>  do
          let res = and $ map (\x => elem x cs') (cats st)
          let prompt = if isNil (cats st)
                         then unwords [show l, ":"]
                         else unwords [show l, ":", show (cats st), ":"]
          if res || isNil (cats st)
            then do
              putStrLn $ unwords [prompt, msg]
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
setLoglvl : (Eq a, Show a) => (l : LogLevel n) -> Eff () [LOG a]
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
initLogger : (Eq a, Show a) => (l : LogLevel n)
                            -> (cs : List a)
                            -> Eff () [LOG a]
initLogger l cs = call $ InitLogger l cs

||| Log the given message at the given level and assign it the list of categories.
|||
||| @l The logging level.
||| @cs The logging categories.
||| @m THe message to be logged.
log : (Show a, Eq a) => (l : Nat) -> {auto prf : LTE l 70}
    -> (cs : List a) -> (m : String) -> Eff () [LOG a]
log l cs msg = call $ Log (getProof lvl) cs msg
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
