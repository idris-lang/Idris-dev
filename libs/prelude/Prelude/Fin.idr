module Prelude.Fin

import Builtins

import Prelude.Basics
import Prelude.Bool
import Prelude.Cast
import Prelude.Classes
import Prelude.List
import Prelude.Maybe
import Prelude.Nat
import Prelude.Either
import Prelude.Uninhabited

import Language.Reflection
import Language.Reflection.Errors

%default total

||| Numbers strictly less than some bound.  The name comes from "finite sets".
|||
||| It's probably not a good idea to use `Fin` for arithmetic, and they will be
||| exceedingly inefficient at run time.
||| @ n the upper bound
data Fin : (n : Nat) -> Type where
    FZ : Fin (S k)
    FS : Fin k -> Fin (S k)

instance Uninhabited (Fin Z) where
  uninhabited FZ impossible
  uninhabited (FS f) impossible

FSInjective : (m : Fin k) -> (n : Fin k) -> FS m = FS n -> m = n
FSInjective left _ Refl = Refl

instance Eq (Fin n) where
    (==) FZ FZ = True
    (==) (FS k) (FS k') = k == k'
    (==) _ _ = False

||| There are no elements of `Fin Z`
FinZAbsurd : Fin Z -> Void
FinZAbsurd FZ impossible

FinZElim : Fin Z -> a
FinZElim x = void (FinZAbsurd x)

||| Convert a Fin to a Nat
finToNat : Fin n -> Nat
finToNat FZ = Z
finToNat (FS k) = S (finToNat k)

||| `finToNat` is injective
finToNatInjective : (fm : Fin k) -> (fn : Fin k) -> (finToNat fm) = (finToNat fn) -> fm = fn
finToNatInjective FZ     FZ     Refl = Refl
finToNatInjective (FS m) FZ     Refl impossible
finToNatInjective FZ     (FS n) Refl impossible
finToNatInjective (FS m) (FS n) prf  =
  cong (finToNatInjective m n (succInjective (finToNat m) (finToNat n) prf)) 

instance Cast (Fin n) Nat where
    cast x = finToNat x

||| Convert a Fin to an Integer
finToInteger : Fin n -> Integer
finToInteger FZ     = 0
finToInteger (FS k) = 1 + finToInteger k

instance Cast (Fin n) Integer where
    cast x = finToInteger x

||| Weaken the bound on a Fin by 1
weaken : Fin n -> Fin (S n)
weaken FZ     = FZ
weaken (FS k) = FS (weaken k)

||| Weaken the bound on a Fin by some amount
weakenN : (n : Nat) -> Fin m -> Fin (m + n)
weakenN n FZ = FZ
weakenN n (FS f) = FS (weakenN n f)

||| Attempt to tighten the bound on a Fin.
||| Return `Left` if the bound could not be tightened, or `Right` if it could.
strengthen : Fin (S n) -> Either (Fin (S n)) (Fin n)
strengthen {n = S k} FZ = Right FZ
strengthen {n = S k} (FS i) with (strengthen i)
  strengthen (FS k) | Left x   = Left (FS x)
  strengthen (FS k) | Right x  = Right (FS x)
strengthen f = Left f

||| Add some natural number to a Fin, extending the bound accordingly
||| @ n the previous bound
||| @ m the number to increase the Fin by
shift : (m : Nat) -> Fin n -> Fin (m + n)
shift Z f = f
shift {n=n} (S m) f = FS {k = (m + n)} (shift m f)

||| The largest element of some Fin type
last : Fin (S n)
last {n=Z} = FZ
last {n=S _} = FS last

total FSinjective : {f : Fin n} -> {f' : Fin n} -> (FS f = FS f') -> f = f'
FSinjective Refl = Refl

instance Ord (Fin n) where
  compare  FZ     FZ    = EQ
  compare  FZ    (FS _) = LT
  compare (FS _)  FZ    = GT
  compare (FS x) (FS y) = compare x y
  
instance MinBound (Fin (S n)) where
  minBound = FZ

instance MaxBound (Fin (S n)) where
  maxBound = last


||| Add two Fins, extending the bound
(+) : Fin n -> Fin m -> Fin (n + m)
(+) {n=S n} {m=m} FZ f' = rewrite plusCommutative n m in weaken (weakenN n f')
(+) (FS f) f' = FS (f + f')

||| Substract two Fins, keeping the bound of the minuend
(-) : Fin n -> Fin m -> Fin n
FZ - _ = FZ
f - FZ = f
(FS f) - (FS f') = weaken $ f - f'

||| Multiply two Fins, extending the bound
(*) : Fin n -> Fin m -> Fin (n * m)
(*) {n=Z} f f' = FinZElim f
(*) {m=Z} f f' = FinZElim f'
(*) {n=S n} {m=S m} FZ     f' = FZ
(*) {n=S n} {m=S m} (FS f) f' = f' + (f * f')

-- Construct a Fin from an integer literal which must fit in the given Fin

natToFin : Nat -> (n : Nat) -> Maybe (Fin n)
natToFin Z     (S j) = Just FZ
natToFin (S k) (S j) with (natToFin k j)
                          | Just k' = Just (FS k')
                          | Nothing = Nothing
natToFin _ _ = Nothing

integerToFin : Integer -> (n : Nat) -> Maybe (Fin n)
integerToFin x Z = Nothing -- make sure 'n' is concrete, to save reduction!
integerToFin x n = if x >= 0 then natToFin (cast x) n else Nothing

||| Proof that some `Maybe` is actually `Just`
data IsJust : Maybe a -> Type where
  ItIsJust : IsJust (Just x)

||| Allow overloading of Integer literals for Fin.
||| @ x the Integer that the user typed
||| @ prf an automatically-constructed proof that `x` is in bounds
fromInteger : (x : Integer) ->
              {default ItIsJust
               prf : (IsJust (integerToFin x n))} ->
              Fin n
fromInteger {n} x {prf} with (integerToFin x n)
  fromInteger {n} x {prf = ItIsJust} | Just y = y

%language ErrorReflection

total
finFromIntegerErrors : Err -> Maybe (List ErrorReportPart)
finFromIntegerErrors (CantUnify x tm `(IsJust (integerToFin ~n ~m)) err xs y)
  = Just [ TextPart "When using", TermPart n
         , TextPart "as a literal for a"
         , TermPart `(Fin ~m)
         , SubReport [ TextPart "Could not show that"
                     , TermPart n
                     , TextPart "is less than"
                     , TermPart m
                     ]
         ]
finFromIntegerErrors _ = Nothing

%error_handlers Prelude.Fin.fromInteger prf finFromIntegerErrors
