module Prelude.Fin

import Prelude.Nat
import Prelude.Either

data Fin : Nat -> Type where
    fO : Fin (S k)
    fS : Fin k -> Fin (S k)

instance Eq (Fin n) where
   (==) = eq where
     eq : Fin m -> Fin m -> Bool
     eq fO fO = True
     eq (fS k) (fS k') = eq k k'
     eq _ _ = False

weaken : Fin n -> Fin (S n)
weaken fO     = fO
weaken (fS k) = fS (weaken k)

strengthen : Fin (S n) -> Either (Fin (S n)) (Fin n)
strengthen {n = S k} fO = Right fO
strengthen {n = S k} (fS i) with (strengthen i)
  strengthen (fS k) | Left x   = Left (fS x)
  strengthen (fS k) | Right x  = Right (fS x)
strengthen f = Left f
