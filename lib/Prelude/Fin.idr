module Prelude.Fin

import Prelude.Nat

data Fin : Nat -> Set where
    fO : Fin (S k)
    fS : Fin k -> Fin (S k)

instance Eq (Fin n) where
   (==) = eq where
     eq : Fin m -> Fin m -> Bool
     eq fO fO = True
     eq (fS k) (fS k') = eq k k'
     eq _ _ = False

wkn : Fin n -> Fin (S n)
wkn fO = fO
wkn (fS k) = fS (wkn k)

