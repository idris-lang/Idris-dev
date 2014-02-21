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

FinZAbsurd : Fin Z -> _|_
FinZAbsurd fZ impossible

FinZElim : Fin Z -> a
FinZElim x = FalseElim (FinZAbsurd x)

finToNat : Fin n -> Nat
finToNat fZ = Z
finToNat (fS k) = S (finToNat k)

instance Cast (Fin n) Nat where
    cast x = finToNat x

finToInteger : Fin n -> Integer
finToInteger fZ     = 0
finToInteger (fS k) = 1 + finToInteger k

instance Cast (Fin n) Integer where
    cast x = finToInteger x

weaken : Fin n -> Fin (S n)
weaken fZ     = fZ
weaken (fS k) = fS (weaken k)

weakenN : (n : Nat) -> Fin m -> Fin (m + n)
weakenN n fZ = fZ
weakenN n (fS f) = fS (weakenN n f)

strengthen : Fin (S n) -> Either (Fin (S n)) (Fin n)
strengthen {n = S k} fZ = Right fZ
strengthen {n = S k} (fS i) with (strengthen i)
  strengthen (fS k) | Left x   = Left (fS x)
  strengthen (fS k) | Right x  = Right (fS x)
strengthen f = Left f

shift : (m : Nat) -> Fin n -> Fin (m + n)
shift Z f = f
shift {n=n} (S m) f = fS {k = (m + n)} (shift m f)

last : Fin (S n)
last {n=Z} = fZ
last {n=S _} = fS last

total fSinjective : {f : Fin n} -> {f' : Fin n} -> (fS f = fS f') -> f = f'
fSinjective refl = refl


instance MinBound (Fin (S n)) where
  minBound = fZ

instance MaxBound (Fin (S n)) where
  maxBound = last


-- Construct a Fin from an integer literal which must fit in the given Fin

natToFin : Nat -> (n : Nat) -> Maybe (Fin n)
natToFin Z     (S j) = Just fZ
natToFin (S k) (S j) with (natToFin k j)
                          | Just k' = Just (fS k')
                          | Nothing = Nothing
natToFin _ _ = Nothing

integerToFin : Integer -> (n : Nat) -> Maybe (Fin n)
integerToFin x n = if x >= 0 then natToFin (cast x) n else Nothing

data IsJust : Maybe a -> Type where
     ItIsJust : IsJust {a} (Just x)

fromInteger : (x : Integer) ->
        {default ItIsJust
             prf : (IsJust (integerToFin x n))} -> Fin n
fromInteger {n} x {prf} with (integerToFin x n)
  fromInteger {n} x {prf = ItIsJust} | Just y = y

