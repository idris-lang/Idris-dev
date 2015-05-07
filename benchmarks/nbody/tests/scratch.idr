module Main

import System 
import Effects
import Effect.State
import Data.Floats
import Data.Fin
import Data.Vect
import Data.Vect.Quantifiers
import Decidable.Equality

fpow : (a -> a) -> Nat -> (a -> a)
fpow f n = foldr1 (.) (replicate n f)

op : Integer -> Integer
op x = x * x + x

test_r : Integer
test_r = (fpow op 4) 3

main : Integer
main = test_r

Velocity : Type
Velocity = Vect 3 Float

Position : Type 
Position = Vect 3 Float

nbody : Nat ->
        {[ 'SunV ::: STATE Velocity,
           'SunP ::: STATE Position,
           'JupiterV ::: STATE Velocity,
           'JupiterP ::: STATE Position,
           'SaturnV ::: STATE Velocity,
           'SaturnP ::: STATE Position,
           'UranusV ::: STATE Velocity,
           'UranusP ::: STATE Position,
           'NeptuneV ::: STATE Velocity,
           'NeptuneP ::: STATE Position ]} Eff $ List Float
nbody = do
  'SunV :- put [1,2,3]
  pure [1.5]

