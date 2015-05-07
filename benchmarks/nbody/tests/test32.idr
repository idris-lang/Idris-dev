module Main

--import System
--import Effects
--import Effect.State
import Data.Floats
--import Data.Fin
import Data.Vect
import Data.Vect.Quantifiers
import Decidable.Equality
import Control.Algebra

main : Bool
main = True

Velocity : Type
Velocity = Vect 3 Float

Position : Type
Position = Vect 3 Float

infixl 8 \+/,\-/
infixl 9 /*/,\*\

(\+/) : Num a => Vect n a -> Vect n a -> Vect n a 
xs \+/ ys = [| xs + ys |]

(\-/) : Num a => Vect n a -> Vect n a -> Vect n a 
xs \-/ ys = [| xs - ys |]

(/*/) : Num a => a -> Vect n a -> Vect n a
s /*/ xs = map (*s) xs

(\*\) : Num a => Vect n a -> a -> Vect n a
xs \*\ s = s /*/ xs

(<+>) : Vect n a -> Vect n a -> Vect n a

instance Field a => Semigroup (Vect n a) where
  xs <+> ys = [| xs + yx |]

instance Field a => 

class Semigroup a => Monoid a where
  neutral : a

class Monoid a => Group a where
  inverse : a -> a

instance Field a => Group (Vect (n:Nat) a) where
  inverse xs = 

instance Field a => Neg (Vect n a) where
  negate xs = (replicate n 0) \-/ xs

instance AbelianGroup x => Vect n x

instance VectorSpace a Float 

--infixl 8 /-\

{-
nbody : {[ 'SunV ::: STATE Velocity, 'SunP ::: STATE Position,
           'JupiterV ::: STATE Velocity, 'JupiterP ::: STATE Position,
           'SaturnV ::: STATE Velocity, 'SaturnP ::: STATE Position,
           'UranusV ::: STATE Velocity, 'UranusP ::: STATE Position,
           'NeptuneV ::: STATE Velocity, 'NeptuneP ::: STATE Position ]} 
           Eff (List Float)
nbody = do pure [1.5]
-}

