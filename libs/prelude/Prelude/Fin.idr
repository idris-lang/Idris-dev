module Prelude.Fin

import Prelude.Nat
import Prelude.Either
import Prelude.Uninhabited

%default total

||| Numbers strictly less than some bound.  The name comes from "finite sets".
|||
||| It's probably not a good idea to use `Fin` for arithmetic, and they will be
||| exceedingly inefficient at run time.
||| @ n the upper bound
data Fin : (n : Nat) -> Type where
    fZ : Fin (S k)
    fS : Fin k -> Fin (S k)

instance Uninhabited (Fin Z) where
  uninhabited fZ impossible
  uninhabited (fS f) impossible

fSInjective : (m : Fin k) -> (n : Fin k) -> fS m = fS n -> m = n
fSInjective left _ refl = refl

instance Eq (Fin n) where
    (==) fZ fZ = True
    (==) (fS k) (fS k') = k == k'
    (==) _ _ = False

||| There are no elements of `Fin Z`
FinZAbsurd : Fin Z -> _|_
FinZAbsurd fZ impossible

FinZElim : Fin Z -> a
FinZElim x = FalseElim (FinZAbsurd x)

||| Convert a Fin to a Nat
finToNat : Fin n -> Nat
finToNat fZ = Z
finToNat (fS k) = S (finToNat k)

||| `finToNat` is injective
finToNatInjective : (fm : Fin k) -> (fn : Fin k) -> (finToNat fm) = (finToNat fn) -> fm = fn
finToNatInjective fZ     fZ     refl = refl
finToNatInjective (fS m) fZ     refl impossible
finToNatInjective fZ     (fS n) refl impossible
finToNatInjective (fS m) (fS n) prf  =
  cong (finToNatInjective m n (succInjective (finToNat m) (finToNat n) prf)) 

instance Cast (Fin n) Nat where
    cast x = finToNat x

||| Convert a Fin to an Integer
finToInteger : Fin n -> Integer
finToInteger fZ     = 0
finToInteger (fS k) = 1 + finToInteger k

instance Cast (Fin n) Integer where
    cast x = finToInteger x

||| Weaken the bound on a Fin by 1
weaken : Fin n -> Fin (S n)
weaken fZ     = fZ
weaken (fS k) = fS (weaken k)

||| Weaken the bound on a Fin by some amount
weakenN : (n : Nat) -> Fin m -> Fin (m + n)
weakenN n fZ = fZ
weakenN n (fS f) = fS (weakenN n f)

||| Attempt to tighten the bound on a Fin.
||| Return `Left` if the bound could not be tightened, or `Right` if it could.
strengthen : Fin (S n) -> Either (Fin (S n)) (Fin n)
strengthen {n = S k} fZ = Right fZ
strengthen {n = S k} (fS i) with (strengthen i)
  strengthen (fS k) | Left x   = Left (fS x)
  strengthen (fS k) | Right x  = Right (fS x)
strengthen f = Left f

||| Add some natural number to a Fin, extending the bound accordingly
||| @ n the previous bound
||| @ m the number to increase the Fin by
shift : (m : Nat) -> Fin n -> Fin (m + n)
shift Z f = f
shift {n=n} (S m) f = fS {k = (m + n)} (shift m f)

||| The largest element of some Fin type
last : Fin (S n)
last {n=Z} = fZ
last {n=S _} = fS last

total fSinjective : {f : Fin n} -> {f' : Fin n} -> (fS f = fS f') -> f = f'
fSinjective refl = refl

instance Ord (Fin n) where
  compare  fZ     fZ    = EQ
  compare  fZ    (fS _) = LT
  compare (fS _)  fZ    = GT
  compare (fS x) (fS y) = compare x y
  
instance MinBound (Fin (S n)) where
  minBound = fZ

instance MaxBound (Fin (S n)) where
  maxBound = last


||| Add two Fins, extending the bound
(+) : Fin n -> Fin m -> Fin (n + m)
(+) {n=S n} {m=m} fZ f' = rewrite plusCommutative n m in weaken (weakenN n f')
(+) (fS f) f' = fS (f + f')

||| Substract two Fins, keeping the bound of the minuend
(-) : Fin n -> Fin m -> Fin n
fZ - _ = fZ
f - fZ = f
(fS f) - (fS f') = weaken $ f - f'

||| Multiply two Fins, extending the bound
(*) : Fin n -> Fin m -> Fin (n * m)
(*) {n=Z} f f' = FinZElim f
(*) {m=Z} f f' = FinZElim f'
(*) {n=S n} {m=S m} fZ     f' = fZ
(*) {n=S n} {m=S m} (fS f) f' = f' + (f * f')

-- Construct a Fin from an integer literal which must fit in the given Fin

natToFin : Nat -> (n : Nat) -> Maybe (Fin n)
natToFin Z     (S j) = Just fZ
natToFin (S k) (S j) with (natToFin k j)
                          | Just k' = Just (fS k')
                          | Nothing = Nothing
natToFin _ _ = Nothing

integerToFin : Integer -> (n : Nat) -> Maybe (Fin n)
integerToFin x n = if x >= 0 then natToFin (cast x) n else Nothing

||| Proof that some `Maybe` is actually `Just`
data IsJust : Maybe a -> Type where
  ItIsJust : IsJust {a} (Just x)

||| Allow overloading of Integer literals for Fin.
||| @ x the Integer that the user typed
||| @ prf an automatically-constructed proof that `x` is in bounds
fromInteger : (x : Integer) ->
              {default ItIsJust
               prf : (IsJust (integerToFin x n))} ->
              Fin n
fromInteger {n} x {prf} with (integerToFin x n)
  fromInteger {n} x {prf = ItIsJust} | Just y = y

