-- ------------------------------------------------------------- [ Default.idr ]
-- Module    : Default.idr
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
module Effect.Logging.Default

import Effects
import public Effect.Logging.Level

import Control.IOExcept -- TODO Add IOExcept Logger.

||| A Logging effect to log levels and categories.
data Logging : Effect where
    Log : (Eq a, Show a) =>
          (lvl : Nat)
       -> (cats : List a)
       -> (msg : String)
       -> Logging () (Nat,List a) (\v => (Nat,List a))

||| The Logging effect.
|||
||| @cTy The type used to differentiate categories.
LOG : (cTy : Type) -> EFFECT
LOG a = MkEff (Nat, List a) Logging

instance Handler Logging IO where
    handle (l,cs) (Log lvl cs' msg) k = do
      case lvl <= l  of
        False => k () (l,cs)
        True  =>  do
          let res = and $ map (\x => elem x cs') cs
          let prompt = if isNil cs then "" else show cs
          if res || isNil cs
            then do
              printLn $ unwords [show lvl, ":", prompt, ":", msg]
              k () (l,cs)
            else k () (l,cs)

||| Log the given message at the given level and assign it the list of categories.
|||
||| @l The logging level.
||| @cs The logging categories.
||| @m THe message to be logged.
log : (Show a, Eq a) => (l : Nat)
    -> (cs : List a) -> (m : String) -> Eff () [LOG a]
log lvl cs msg = call $ Log lvl cs msg

-- --------------------------------------------------------------------- [ EOF ]
