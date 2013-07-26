module Prelude.Fin

import Prelude.Nat
import Prelude.Either

data Fin : Nat -> Type where
    fO : Fin (S k)
    fS : Fin k -> Fin (S k)

instance Eq (Fin n) where
    (==) fO fO = True
    (==) (fS k) (fS k') = k == k'
    (==) _ _ = False

finToNat : Fin n -> Nat -> Nat
finToNat fO a = a
finToNat (fS x) a = finToNat x (S a)

instance Cast (Fin n) Nat where
    cast x = finToNat x Z

finToInt : Fin n -> Integer -> Integer
finToInt fO a = a
finToInt (fS x) a = finToInt x (a + 1)

instance Cast (Fin n) Integer where
    cast x = finToInt x 0

weaken : Fin n -> Fin (S n)
weaken fO     = fO
weaken (fS k) = fS (weaken k)

strengthen : Fin (S n) -> Either (Fin (S n)) (Fin n)
strengthen {n = S k} fO = Right fO
strengthen {n = S k} (fS i) with (strengthen i)
  strengthen (fS k) | Left x   = Left (fS x)
  strengthen (fS k) | Right x  = Right (fS x)
strengthen f = Left f

last : Fin (S n)
last {n=Z} = fO
last {n=S _} = fS last

total fSinjective : {f : Fin n} -> {f' : Fin n} -> (fS f = fS f') -> f = f'
fSinjective refl = refl


-- Construct a Fin from an integer literal which must fit in the given Fin

natToFin : Nat -> (n : Nat) -> Maybe (Fin n)
natToFin Z     (S j) = Just fO
natToFin (S k) (S j) with (natToFin k j)
                          | Just k' = Just (fS k')
                          | Nothing = Nothing
natToFin _ _ = Nothing

integerToFin : Integer -> (n : Nat) -> Maybe (Fin n)
integerToFin x = natToFin (cast x)

data IsJust : Maybe a -> Type where
     ItIsJust : IsJust {a} (Just x) 

fromInteger : (x : Integer) -> 
        {default (ItIsJust _ _) 
             prf : (IsJust (integerToFin x n))} -> Fin n
fromInteger {n} x {prf} with (integerToFin x n)
  fromInteger {n} x {prf = ItIsJust} | Just y = y

