-- --------------------------------------------------------------- [ Level.idr ]
-- Module    : Level.idr
-- Copyright : (c) The Idris Community
-- License   : see LICENSE
-- --------------------------------------------------------------------- [ EOH ]
||| A dependently typed logging level representation where logging
||| levels are based on a Natural number range [0,70].
|||
||| The `LogLevel` type allows for semantic constructors to be used
||| for the majority of logging levels, with an option for custom
||| levels to be defined.
|||
||| The logging level design comes from the Log4j/Python family of
||| loggers.
module Effect.Logging.Level

%access public export
%default total

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

implementation Cast (LogLevel n) Nat where
  cast {n} _ = n

implementation Show (LogLevel n) where
  show OFF        = "OFF"
  show TRACE      = "TRACE"
  show DEBUG      = "DEBUG"
  show INFO       = "INFO"
  show WARN       = "WARN"
  show FATAL      = "FATAL"
  show ERROR      = "ERROR"
  show ALL        = "ALL"
  show (CUSTOM n) = unwords ["CUSTOM", show n]

implementation Eq (LogLevel n) where
  (==) x y = lvlEq x y
    where
      lvlEq : LogLevel a -> LogLevel b -> Bool
      lvlEq {a} {b} _ _ = a == b

||| Compare to logging levels.
cmpLevel : LogLevel a -> LogLevel b -> Ordering
cmpLevel {a} {b} _ _ = compare a b

-- --------------------------------------------------------------------- [ EOF ]
