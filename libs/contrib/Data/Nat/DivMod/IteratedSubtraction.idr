||| Division of natural numbers, by iterated subtraction using well-founded
||| recursion
module Data.Nat.DivMod.IteratedSubtraction

import Data.Fin
import Data.So

%default total
%access public export

||| A strict less-than relation on `Nat`.
|||
||| @ n the smaller number
||| @ m the larger number
data LT' : (n,m : Nat) -> Type where
  ||| n < 1 + n
  LTSucc : LT' n (S n)
  ||| n < m implies that n < m + 1
  LTStep : LT' n m -> LT' n (S m)

%name LT' lt, lt'

||| Nothing is strictly less than zero
implementation Uninhabited (LT' n 0) where
  uninhabited LTSucc impossible

||| Zero is less than any non-zero number.
LTZeroLeast : LT' Z (S n)
LTZeroLeast {n = Z}   = LTSucc
LTZeroLeast {n = S n} = LTStep LTZeroLeast

||| If n < m, then 1 + n < 1 + m
ltSuccSucc : LT' n m -> LT' (S n) (S m)
ltSuccSucc LTSucc      = LTSucc
ltSuccSucc (LTStep lt) = LTStep $ ltSuccSucc lt

||| If n + 1 < m, then n < m
lteToLt' : LTE (S n) m -> LT' n m
lteToLt' {n = Z}   (LTESucc x) = LTZeroLeast
lteToLt' {n = S k} (LTESucc x) = ltSuccSucc $ lteToLt' x

||| Convert from LT' to LTE
ltToLTE : LT' n m -> LTE (S n) m
ltToLTE LTSucc      = lteRefl
ltToLTE (LTStep lt) = lteSuccRight $ ltToLTE lt

||| Subtraction gives a result that is actually smaller.
minusLT' : (x,y : Nat) -> minus x y `LT'` S x
minusLT' Z     y = LTSucc
minusLT' (S k) Z = LTSucc
minusLT' (S k) (S j) = LTStep (minusLT' k j)

||| Strict less-than is well-founded, with the cascade stopping at
||| zero (because there's nothing less than zero). This can't be done
||| for LTE, because that one doesn't stop at zero (because `LTE 0 0`
||| is inhabited).
implementation WellFounded LT' where
  wellFounded x = Access (acc x)
    where
      ||| Show accessibility by induction on the structure of the LT' witness
      acc : (x, y : Nat) -> LT' y x -> Accessible LT' y
      -- Zero is vacuously accessible: there's nothing smaller to check
      acc Z     y lt = absurd lt
      -- If the element being accessed is one smaller, we're done
      acc (S y) y LTSucc = Access (acc y)
      -- If the element is more than one smaller, we need to go further
      acc (S k) y (LTStep smaller) = acc k y smaller

||| The result of division on natural numbers.
|||
||| @ dividend the dividend
||| @ divisor the divisor
data DivMod : (dividend, divisor : Nat) -> Type where
  ||| The result of division, with a quotient and a remainder.
  |||
  ||| @ dividend the dividend
  ||| @ divisor the divisor
  ||| @ quotient the quotient
  ||| @ remainder the remainder (bounded by the divisor)
  ||| @ ok the fact that this is, in fact, a result of division
  DivModRes : {dividend, divisor : Nat} ->
              (quotient : Nat) -> (remainder : Fin divisor) ->
              (ok : dividend = finToNat remainder + quotient * divisor) ->
              DivMod dividend divisor


||| Any natural number can be a `Fin` where the bound is itself plus some difference.
private
toFin : (x : Nat) -> (diff : Nat) -> Fin (plus x (S diff))
toFin Z diff = FZ
toFin (S k) diff = FS $ toFin k diff

||| Converting to a `Fin` and back to `Nat` preserves the input. This is a correctness proof for `toFin`.
private
toFinAndBack : (x : Nat) -> (diff : Nat) -> finToNat (toFin x diff) = x
toFinAndBack Z diff = Refl
toFinAndBack (S k) diff = cong (toFinAndBack k diff)


||| The accessibilty predicate used for division.
private
accPlusLT' : LT' (S j) (S (plus k (S j)))
accPlusLT' {j = Z}   {k = Z}   = LTSucc
accPlusLT' {j = Z}   {k = S k} = LTStep (accPlusLT' {j = Z} {k = k})
accPlusLT' {j = S j} {k = k}   = rewrite sym $ plusSuccRightSucc k (S j) in
                                 ltSuccSucc accPlusLT'


||| Division and modulus on `Nat`, inspired by the definition in the
||| Agda standard library.
|||
||| This uses well-founded recursion on `LT'`.
|||
||| @ dividend the dividend
||| @ divisor the divisor
||| @ nonzero division by zero is nonsense
total -- yay!
divMod : (dividend, divisor : Nat) ->
         {auto nonzero : So (not (decAsBool (decEq divisor Z)))} ->
         DivMod dividend divisor
divMod _     Z     {nonzero} = absurd nonzero
divMod Z     (S k)           = DivModRes 0 FZ Refl
divMod (S j) (S k) {nonzero} = wfInd {P=P} stepDiv (S j) (S k) nonzero
  where
    ||| The goal passed to the accessibility eliminator.
    |||
    ||| This is responsible for generating the goal in the
    ||| well-founded fixed point.
    |||
    ||| @ dividend the dividend to recurse over
    P : (dividend : Nat) -> Type
    P dividend = (divisor : Nat) -> (nonzero : So (not (decAsBool (decEq divisor Z)))) -> DivMod dividend divisor


    ||| Well-founded recursion needs a recursion operator.
    |||
    ||| @ dividend the dividend we are recursing over
    ||| @ rec the recursive call provided by the well-founded induction operator
    stepDiv : (dividend : Nat) -> (rec : (d' : Nat) -> LT' d' dividend -> P d') -> P dividend
    -- We need not consider division by zero
    stepDiv dividend rec   Z     nonzero = absurd nonzero
    -- Dividing zero by anyting else gives 0, with 0 remainder
    stepDiv Z rec (S k) nonzero = DivModRes 0 0 Refl
    -- To divide two non-zero values, we must know which is larger
    stepDiv (S j) rec (S k) nonzero with (cmp j k)
      -- n / n = 1 remainder 0
      stepDiv (S j)                 rec (S j)                 nonzero | CmpEQ      =
        DivModRes 1 0 (sym $ cong (plusZeroRightNeutral j))
      -- if n < m, then m = n + r, and the quotient is 0 with remainder r
      stepDiv (S j)                 rec (S (plus j (S diff))) nonzero | CmpLT diff =
        DivModRes 0 (toFin (S j) diff) $
          rewrite toFinAndBack j diff
          in sym $ cong (plusZeroRightNeutral j)
      -- if n > m, then n = m + d, and the quotient is 1 + ((n - m) / m) with the same remainder
      stepDiv (S (plus k (S diff))) rec (S k)                 nonzero | CmpGT diff =
        let res = rec (S diff) accPlusLT' (S k) Oh
        in case res of
             DivModRes quotient remainder ok =>
               DivModRes (S quotient) remainder $
                 rewrite plusAssociative (finToNat remainder) (S k) (mult quotient (S k)) in
                 rewrite plusCommutative (finToNat remainder) (S k) in
                 rewrite sym $ plusAssociative (S k) (finToNat remainder) (mult quotient (S k)) in
                 rewrite ok in Refl


