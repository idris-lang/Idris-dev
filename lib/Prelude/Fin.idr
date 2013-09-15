module Prelude.Fin

import Prelude.Nat
import Prelude.Either

%default total

data Fin : Nat -> Type where
    fZ : Fin (S k)
    fS : Fin k -> Fin (S k)

instance Eq (Fin n) where
    (==) fZ fZ = True
    (==) (fS k) (fS k') = k == k'
    (==) _ _ = False

finToNat : Fin n -> Nat -> Nat
finToNat fZ a = a
finToNat (fS x) a = finToNat x (S a)

instance Cast (Fin n) Nat where
    cast x = finToNat x Z

finToInt : Fin n -> Integer -> Integer
finToInt fZ a = a
finToInt (fS x) a = finToInt x (a + 1)

instance Cast (Fin n) Integer where
    cast x = finToInt x 0

weaken : Fin n -> Fin (n + m)
weaken fZ     = fZ
weaken (fS k) = fS (weaken k)

strengthen : Fin (S n) -> Either (Fin (S n)) (Fin n)
strengthen {n = S k} fZ = Right fZ
strengthen {n = S k} (fS i) with (strengthen i)
  strengthen (fS k) | Left x   = Left (fS x)
  strengthen (fS k) | Right x  = Right (fS x)
strengthen f = Left f

last : Fin (S n)
last {n=Z} = fZ
last {n=S _} = fS last

fSinjective : {f : Fin n} -> {f' : Fin n} -> (fS f = fS f') -> f = f'
fSinjective refl = refl


-- Construct a Fin from an integer literal which must fit in the given Fin

natToFin : Nat -> (n : Nat) -> Maybe (Fin n)
natToFin Z     (S j) = Just fZ
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

