-- -------------------------------------------------------------- [ Levels.idr ]
-- Module    : Levels.idr
-- Copyright : (c) Jan de Muijnck-Hughes
-- License   : see LICENSE
-- --------------------------------------------------------------------- [ EOH ]
||| Common aliases and definitions of Logging Levels.
module Effect.Logging.Level

%access public
-- ---------------------------------------------- [ Nat Derived Logging Levels ]
--
-- Several aliases have been defined to aide in semantic use of the
-- logging levels. These aliases have come from the Log4j family of
-- loggers.

||| No events will be logged.
OFF : Nat
OFF = 0

||| A severe error that will prevent the application from continuing.
FATAL : Nat
FATAL = 1

||| An error in the application, possibly recoverable.
ERROR : Nat
ERROR = 2

||| An event that might possible lead to an error.
WARN : Nat
WARN = 3

|||  An event for informational purposes.
INFO : Nat
INFO = 4

||| A general debugging event.
DEBUG : Nat
DEBUG = 5

||| A fine-grained debug message, typically capturing the flow through
||| the application.
TRACE : Nat
TRACE = 6

||| All events should be logged.
ALL : Nat
ALL = 7

-- --------------------------------------------------------------------- [ EOF ]
