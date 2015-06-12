module Prelude.Nat

import Builtins

import Prelude.Algebra
import Prelude.Basics
import Prelude.Bool
import Prelude.Cast
import Prelude.Classes
import Prelude.Uninhabited

%access public
%default total

||| Unary natural numbers
%elim data Nat =
  ||| Zero
  Z |
  ||| Successor
  S Nat

-- name hints for interactive editing
%name Nat k,j,i,n,m

instance Uninhabited (Z = S n) where
  uninhabited Refl impossible

--------------------------------------------------------------------------------
-- Syntactic tests
--------------------------------------------------------------------------------

total isZero : Nat -> Bool
isZero Z     = True
isZero (S n) = False

total isSucc : Nat -> Bool
isSucc Z     = False
isSucc (S n) = True

--------------------------------------------------------------------------------
-- Basic arithmetic functions
--------------------------------------------------------------------------------

||| Add two natural numbers.
||| @ n the number to case-split on
||| @ m the other number
total plus : (n, m : Nat) -> Nat
plus Z right        = right
plus (S left) right = S (plus left right)

||| Multiply natural numbers
total mult : Nat -> Nat -> Nat
mult Z right        = Z
mult (S left) right = plus right $ mult left right

||| Convert an Integer to a Nat, mapping negative numbers to 0
fromIntegerNat : Integer -> Nat
fromIntegerNat 0 = Z
fromIntegerNat n =
  if (n > 0) then
    S (fromIntegerNat (assert_smaller n (n - 1)))
  else
    Z

||| Convert a Nat to an Integer
toIntegerNat : Nat -> Integer
toIntegerNat Z = 0
toIntegerNat (S k) = 1 + toIntegerNat k

||| Subtract natural numbers. If the second number is larger than the first, return 0.
total minus : Nat -> Nat -> Nat
minus Z        right     = Z
minus left     Z         = left
minus (S left) (S right) = minus left right

||| Exponentiation of natural numbers
total power : Nat -> Nat -> Nat
power base Z       = S Z
power base (S exp) = mult base $ power base exp

hyper : Nat -> Nat -> Nat -> Nat
hyper Z        a b      = S b
hyper (S Z)    a Z      = a
hyper (S(S Z)) a Z      = Z
hyper n        a Z      = S Z
hyper (S pn)   a (S pb) = hyper pn a (hyper (S pn) a pb)


--------------------------------------------------------------------------------
-- Comparisons
--------------------------------------------------------------------------------

||| Proofs that `n` is less than or equal to `m`
||| @ n the smaller number
||| @ m the larger number
data LTE  : (n, m : Nat) -> Type where
  ||| Zero is the smallest Nat
  LTEZero : LTE Z    right
  ||| If n <= m, then n + 1 <= m + 1
  LTESucc : LTE left right -> LTE (S left) (S right)

instance Uninhabited (LTE (S n) Z) where
  uninhabited LTEZero impossible

||| Greater than or equal to
total GTE : Nat -> Nat -> Type
GTE left right = LTE right left

||| Strict less than
total LT : Nat -> Nat -> Type
LT left right = LTE (S left) right

||| Strict greater than
total GT : Nat -> Nat -> Type
GT left right = LT right left

||| A successor is never less than or equal zero
succNotLTEzero : Not (S m `LTE` Z)
succNotLTEzero LTEZero impossible

||| If two numbers are ordered, their predecessors are too
fromLteSucc : (S m `LTE` S n) -> (m `LTE` n)
fromLteSucc (LTESucc x) = x

||| A decision procedure for `LTE`
isLTE : (m, n : Nat) -> Dec (m `LTE` n)
isLTE Z n = Yes LTEZero
isLTE (S k) Z = No succNotLTEzero
isLTE (S k) (S j) with (isLTE k j)
  isLTE (S k) (S j) | (Yes prf) = Yes (LTESucc prf)
  isLTE (S k) (S j) | (No contra) = No (contra . fromLteSucc)

||| `LTE` is reflexive.
lteRefl : LTE n n
lteRefl {n = Z}   = LTEZero
lteRefl {n = S k} = LTESucc lteRefl

||| n < m implies n < m + 1
lteSuccRight : LTE n m -> LTE n (S m)
lteSuccRight LTEZero     = LTEZero
lteSuccRight (LTESucc x) = LTESucc (lteSuccRight x)


||| Boolean test than one Nat is less than or equal to another
total lte : Nat -> Nat -> Bool
lte Z        right     = True
lte left     Z         = False
lte (S left) (S right) = lte left right

||| Boolean test than one Nat is greater than or equal to another
total gte : Nat -> Nat -> Bool
gte left right = lte right left

||| Boolean test than one Nat is strictly less than another
total lt : Nat -> Nat -> Bool
lt left right = lte (S left) right

||| Boolean test than one Nat is strictly greater than another
total gt : Nat -> Nat -> Bool
gt left right = lt right left

||| Find the least of two natural numbers
total minimum : Nat -> Nat -> Nat
minimum Z m = Z
minimum (S n) Z = Z
minimum (S n) (S m) = S (minimum n m)

||| Find the greatest of two natural numbers
total maximum : Nat -> Nat -> Nat
maximum Z m = m
maximum (S n) Z = S n
maximum (S n) (S m) = S (maximum n m)

||| Tail recursive cast Nat to Int
||| Note that this can overflow
toIntNat : Nat -> Int
toIntNat n = toIntNat' n 0 where
	toIntNat' : Nat -> Int -> Int
	toIntNat' Z     x = x
	toIntNat' (S n) x = toIntNat' n (x + 1)

--------------------------------------------------------------------------------
-- Type class instances
--------------------------------------------------------------------------------

instance Eq Nat where
  Z == Z         = True
  (S l) == (S r) = l == r
  _ == _         = False

instance Cast Nat Integer where
  cast = toIntegerNat

instance Ord Nat where
  compare Z Z         = EQ
  compare Z (S k)     = LT
  compare (S k) Z     = GT
  compare (S x) (S y) = compare x y

instance Num Nat where
  (+) = plus
  (-) = minus
  (*) = mult

  abs x = x

  fromInteger = fromIntegerNat

instance MinBound Nat where
  minBound = Z

||| Casts negative `Integers` to 0.
instance Cast Integer Nat where
  cast = fromInteger

||| A wrapper for Nat that specifies the semigroup and monad instances that use (+)
record Multiplicative where
  constructor getMultiplicative
  _ : Nat

||| A wrapper for Nat that specifies the semigroup and monad instances that use (*)
record Additive where
  constructor getAdditive  
  _ : Nat
  
instance Semigroup Multiplicative where
  (<+>) left right = getMultiplicative $ left' * right'
    where
      left'  : Nat
      left'  =
       case left of
          getMultiplicative m => m

      right' : Nat
      right' =
        case right of
          getMultiplicative m => m

instance Semigroup Additive where
  left <+> right = getAdditive $ left' + right'
    where
      left'  : Nat
      left'  =
        case left of
          getAdditive m => m

      right' : Nat
      right' =
        case right of
          getAdditive m => m

instance Monoid Multiplicative where
  neutral = getMultiplicative $ S Z

instance Monoid Additive where
  neutral = getAdditive Z

||| Casts negative `Ints` to 0.
instance Cast Int Nat where
  cast i = fromInteger (cast i)

instance Cast Nat Int where
  cast = toIntNat

--------------------------------------------------------------------------------
-- Auxilliary notions
--------------------------------------------------------------------------------

||| The predecessor of a natural number. `pred Z` is `Z`.
total pred : Nat -> Nat
pred Z     = Z
pred (S n) = n

--------------------------------------------------------------------------------
-- Fibonacci and factorial
--------------------------------------------------------------------------------

||| Fibonacci numbers
total fib : Nat -> Nat
fib Z         = Z
fib (S Z)     = S Z
fib (S (S n)) = fib (S n) + fib n

||| Factorial function
total fact : Nat -> Nat
fact Z     = S Z
fact (S n) = (S n) * fact n

--------------------------------------------------------------------------------
-- Division and modulus
--------------------------------------------------------------------------------

SIsNotZ : {x: Nat} -> (S x = Z) -> Void
SIsNotZ Refl impossible

modNatNZ : Nat -> (y: Nat) -> Not (y = Z) -> Nat
modNatNZ left Z         p = void (p Refl)
modNatNZ left (S right) _ = mod' left left right
  where
    total mod' : Nat -> Nat -> Nat -> Nat
    mod' Z        centre right = centre
    mod' (S left) centre right =
      if lte centre right then
        centre
      else
        mod' left (centre - (S right)) right

partial
modNat : Nat -> Nat -> Nat
modNat left (S right) = modNatNZ left (S right) SIsNotZ

divNatNZ : Nat -> (y: Nat) -> Not (y = Z) -> Nat
divNatNZ left Z         p = void (p Refl)
divNatNZ left (S right) _ = div' left left right
  where
    total div' : Nat -> Nat -> Nat -> Nat
    div' Z        centre right = Z
    div' (S left) centre right =
      if lte centre right then
        Z
      else
        S (div' left (centre - (S right)) right)

partial
divNat : Nat -> Nat -> Nat
divNat left (S right) = divNatNZ left (S right) SIsNotZ

divCeilNZ : Nat -> (y: Nat) -> Not (y = 0) -> Nat
divCeilNZ x y p = case (modNatNZ x y p) of
  Z   => divNatNZ x y p
  S _ => S (divNatNZ x y p)

partial
divCeil : Nat -> Nat -> Nat
divCeil x (S y) = divCeilNZ x (S y) SIsNotZ

instance Integral Nat where
  div = divNat
  mod = modNat

log2NZ : (x: Nat) -> Not (x = Z) -> Nat
log2NZ Z         p = void (p Refl)
log2NZ (S Z)     _ = Z
log2NZ (S (S n)) _ = S (log2NZ (assert_smaller (S (S n)) (S (divNatNZ n 2 SIsNotZ))) SIsNotZ)

partial
log2 : Nat -> Nat
log2 (S n) = log2NZ (S n) SIsNotZ

--------------------------------------------------------------------------------
-- GCD and LCM
--------------------------------------------------------------------------------
partial
gcd : Nat -> Nat -> Nat
gcd a Z = a
gcd a b = assert_total (gcd b (a `modNat` b))

total
lcm : Nat -> Nat -> Nat
lcm x y = case (x, y) of
               (_, Z) => Z
               (Z, _) => Z
               _ => lcm' (x * y) (gcd x y)
  where
    lcm' : Nat -> Nat -> Nat
    lcm' n m with (decEq m Z)
      | Yes prf = Z
      | No prf  = divNatNZ n m prf

--------------------------------------------------------------------------------
-- An informative comparison view
--------------------------------------------------------------------------------
data CmpNat : Nat -> Nat -> Type where
     CmpLT : (y : _) -> CmpNat x (x + S y)
     CmpEQ : CmpNat x x
     CmpGT : (x : _) -> CmpNat (y + S x) y

total cmp : (x, y : Nat) -> CmpNat x y
cmp Z Z     = CmpEQ
cmp Z (S k) = CmpLT _
cmp (S k) Z = CmpGT _
cmp (S x) (S y) with (cmp x y)
  cmp (S x) (S (x + (S k))) | CmpLT k = CmpLT k
  cmp (S x) (S x)           | CmpEQ   = CmpEQ
  cmp (S (y + (S k))) (S y) | CmpGT k = CmpGT k

--------------------------------------------------------------------------------
-- Properties
--------------------------------------------------------------------------------

-- Succ

||| S preserves equality
total eqSucc : (left : Nat) -> (right : Nat) -> (p : left = right) ->
  S left = S right
eqSucc left _ Refl = Refl

||| S is injective
total succInjective : (left : Nat) -> (right : Nat) -> (p : S left = S right) ->
  left = right
succInjective left _ Refl = Refl

-- Plus
total plusZeroLeftNeutral : (right : Nat) -> 0 + right = right
plusZeroLeftNeutral right = Refl

total plusZeroRightNeutral : (left : Nat) -> left + 0 = left
plusZeroRightNeutral Z     = Refl
plusZeroRightNeutral (S n) =
  let inductiveHypothesis = plusZeroRightNeutral n in
    ?plusZeroRightNeutralStepCase

total plusSuccRightSucc : (left : Nat) -> (right : Nat) ->
  S (left + right) = left + (S right)
plusSuccRightSucc Z right        = Refl
plusSuccRightSucc (S left) right =
  let inductiveHypothesis = plusSuccRightSucc left right in
    ?plusSuccRightSuccStepCase

total plusCommutative : (left : Nat) -> (right : Nat) ->
  left + right = right + left
plusCommutative Z        right = ?plusCommutativeBaseCase
plusCommutative (S left) right =
  let inductiveHypothesis = plusCommutative left right in
    ?plusCommutativeStepCase

total plusAssociative : (left : Nat) -> (centre : Nat) -> (right : Nat) ->
  left + (centre + right) = (left + centre) + right
plusAssociative Z        centre right = Refl
plusAssociative (S left) centre right =
  let inductiveHypothesis = plusAssociative left centre right in
    ?plusAssociativeStepCase

total plusConstantRight : (left : Nat) -> (right : Nat) -> (c : Nat) ->
  (p : left = right) -> left + c = right + c
plusConstantRight left _ c Refl = Refl

total plusConstantLeft : (left : Nat) -> (right : Nat) -> (c : Nat) ->
  (p : left = right) -> c + left = c + right
plusConstantLeft left _ c Refl = Refl

total plusOneSucc : (right : Nat) -> 1 + right = S right
plusOneSucc n = Refl

total plusLeftCancel : (left : Nat) -> (right : Nat) -> (right' : Nat) ->
  (p : left + right = left + right') -> right = right'
plusLeftCancel Z        right right' p = ?plusLeftCancelBaseCase
plusLeftCancel (S left) right right' p =
  let inductiveHypothesis = plusLeftCancel left right right' in
    ?plusLeftCancelStepCase

total plusRightCancel : (left : Nat) -> (left' : Nat) -> (right : Nat) ->
  (p : left + right = left' + right) -> left = left'
plusRightCancel left left' Z         p = ?plusRightCancelBaseCase
plusRightCancel left left' (S right) p =
  let inductiveHypothesis = plusRightCancel left left' right in
    ?plusRightCancelStepCase

total plusLeftLeftRightZero : (left : Nat) -> (right : Nat) ->
  (p : left + right = left) -> right = Z
plusLeftLeftRightZero Z        right p = ?plusLeftLeftRightZeroBaseCase
plusLeftLeftRightZero (S left) right p =
  let inductiveHypothesis = plusLeftLeftRightZero left right in
    ?plusLeftLeftRightZeroStepCase

-- Mult
total multZeroLeftZero : (right : Nat) -> Z * right = Z
multZeroLeftZero right = Refl

total multZeroRightZero : (left : Nat) -> left * Z = Z
multZeroRightZero Z        = Refl
multZeroRightZero (S left) =
  let inductiveHypothesis = multZeroRightZero left in
    ?multZeroRightZeroStepCase

total multRightSuccPlus : (left : Nat) -> (right : Nat) ->
  left * (S right) = left + (left * right)
multRightSuccPlus Z        right = Refl
multRightSuccPlus (S left) right =
  let inductiveHypothesis = multRightSuccPlus left right in
    ?multRightSuccPlusStepCase

total multLeftSuccPlus : (left : Nat) -> (right : Nat) ->
  (S left) * right = right + (left * right)
multLeftSuccPlus left right = Refl

total multCommutative : (left : Nat) -> (right : Nat) ->
  left * right = right * left
multCommutative Z right        = ?multCommutativeBaseCase
multCommutative (S left) right =
  let inductiveHypothesis = multCommutative left right in
    ?multCommutativeStepCase

total multDistributesOverPlusRight : (left : Nat) -> (centre : Nat) -> (right : Nat) ->
  left * (centre + right) = (left * centre) + (left * right)
multDistributesOverPlusRight Z        centre right = Refl
multDistributesOverPlusRight (S left) centre right =
  let inductiveHypothesis = multDistributesOverPlusRight left centre right in
    ?multDistributesOverPlusRightStepCase

total multDistributesOverPlusLeft : (left : Nat) -> (centre : Nat) -> (right : Nat) ->
  (left + centre) * right = (left * right) + (centre * right)
multDistributesOverPlusLeft Z        centre right = Refl
multDistributesOverPlusLeft (S left) centre right =
  let inductiveHypothesis = multDistributesOverPlusLeft left centre right in
    ?multDistributesOverPlusLeftStepCase

total multAssociative : (left : Nat) -> (centre : Nat) -> (right : Nat) ->
  left * (centre * right) = (left * centre) * right
multAssociative Z        centre right = Refl
multAssociative (S left) centre right =
  let inductiveHypothesis = multAssociative left centre right in
    ?multAssociativeStepCase

total multOneLeftNeutral : (right : Nat) -> 1 * right = right
multOneLeftNeutral Z         = Refl
multOneLeftNeutral (S right) =
  let inductiveHypothesis = multOneLeftNeutral right in
    ?multOneLeftNeutralStepCase

total multOneRightNeutral : (left : Nat) -> left * 1 = left
multOneRightNeutral Z        = Refl
multOneRightNeutral (S left) =
  let inductiveHypothesis = multOneRightNeutral left in
    ?multOneRightNeutralStepCase

-- Minus
total minusSuccSucc : (left : Nat) -> (right : Nat) ->
  (S left) - (S right) = left - right
minusSuccSucc left right = Refl

total minusZeroLeft : (right : Nat) -> 0 - right = Z
minusZeroLeft right = Refl

total minusZeroRight : (left : Nat) -> left - 0 = left
minusZeroRight Z        = Refl
minusZeroRight (S left) = Refl

total minusZeroN : (n : Nat) -> Z = n - n
minusZeroN Z     = Refl
minusZeroN (S n) = minusZeroN n

total minusOneSuccN : (n : Nat) -> S Z = (S n) - n
minusOneSuccN Z     = Refl
minusOneSuccN (S n) = minusOneSuccN n

total minusSuccOne : (n : Nat) -> S n - 1 = n
minusSuccOne Z     = Refl
minusSuccOne (S n) = Refl

total minusPlusZero : (n : Nat) -> (m : Nat) -> n - (n + m) = Z
minusPlusZero Z     m = Refl
minusPlusZero (S n) m = minusPlusZero n m

total minusMinusMinusPlus : (left : Nat) -> (centre : Nat) -> (right : Nat) ->
  left - centre - right = left - (centre + right)
minusMinusMinusPlus Z        Z          right = Refl
minusMinusMinusPlus (S left) Z          right = Refl
minusMinusMinusPlus Z        (S centre) right = Refl
minusMinusMinusPlus (S left) (S centre) right =
  let inductiveHypothesis = minusMinusMinusPlus left centre right in
    ?minusMinusMinusPlusStepCase

total plusMinusLeftCancel : (left : Nat) -> (right : Nat) -> (right' : Nat) ->
  (left + right) - (left + right') = right - right'
plusMinusLeftCancel Z right right'        = Refl
plusMinusLeftCancel (S left) right right' =
  let inductiveHypothesis = plusMinusLeftCancel left right right' in
    ?plusMinusLeftCancelStepCase

total multDistributesOverMinusLeft : (left : Nat) -> (centre : Nat) -> (right : Nat) ->
  (left - centre) * right = (left * right) - (centre * right)
multDistributesOverMinusLeft Z        Z          right = Refl
multDistributesOverMinusLeft (S left) Z          right =
  ?multDistributesOverMinusLeftBaseCase
multDistributesOverMinusLeft Z        (S centre) right = Refl
multDistributesOverMinusLeft (S left) (S centre) right =
  let inductiveHypothesis = multDistributesOverMinusLeft left centre right in
    ?multDistributesOverMinusLeftStepCase

total multDistributesOverMinusRight : (left : Nat) -> (centre : Nat) -> (right : Nat) ->
  left * (centre - right) = (left * centre) - (left * right)
multDistributesOverMinusRight left centre right =
  ?multDistributesOverMinusRightBody

-- Power
total powerSuccPowerLeft : (base : Nat) -> (exp : Nat) -> power base (S exp) =
  base * (power base exp)
powerSuccPowerLeft base exp = Refl

total multPowerPowerPlus : (base : Nat) -> (exp : Nat) -> (exp' : Nat) ->
  (power base exp) * (power base exp') = power base (exp + exp')
multPowerPowerPlus base Z       exp' = ?multPowerPowerPlusBaseCase
multPowerPowerPlus base (S exp) exp' =
  let inductiveHypothesis = multPowerPowerPlus base exp exp' in
    ?multPowerPowerPlusStepCase

total powerZeroOne : (base : Nat) -> power base 0 = S Z
powerZeroOne base = Refl

total powerOneNeutral : (base : Nat) -> power base 1 = base
powerOneNeutral Z        = Refl
powerOneNeutral (S base) =
  let inductiveHypothesis = powerOneNeutral base in
    ?powerOneNeutralStepCase

total powerOneSuccOne : (exp : Nat) -> power 1 exp = S Z
powerOneSuccOne Z       = Refl
powerOneSuccOne (S exp) =
  let inductiveHypothesis = powerOneSuccOne exp in
    ?powerOneSuccOneStepCase

total powerSuccSuccMult : (base : Nat) -> power base 2 = mult base base
powerSuccSuccMult Z        = Refl
powerSuccSuccMult (S base) =
  let inductiveHypothesis = powerSuccSuccMult base in
    ?powerSuccSuccMultStepCase

total powerPowerMultPower : (base : Nat) -> (exp : Nat) -> (exp' : Nat) ->
  power (power base exp) exp' = power base (exp * exp')
powerPowerMultPower base exp Z        = ?powerPowerMultPowerBaseCase
powerPowerMultPower base exp (S exp') =
  let inductiveHypothesis = powerPowerMultPower base exp exp' in
    ?powerPowerMultPowerStepCase

-- Pred
total predSucc : (n : Nat) -> pred (S n) = n
predSucc n = Refl

total minusSuccPred : (left : Nat) -> (right : Nat) ->
  left - (S right) = pred (left - right)
minusSuccPred Z        right = Refl
minusSuccPred (S left) Z =
  let inductiveHypothesis = minusSuccPred left Z in
    ?minusSuccPredStepCase
minusSuccPred (S left) (S right) =
  let inductiveHypothesis = minusSuccPred left right in
    ?minusSuccPredStepCase'

-- ifThenElse
total ifThenElseSuccSucc : (cond : Bool) -> (t : Nat) -> (f : Nat) ->
  S (ifThenElse cond t f) = ifThenElse cond (S t) (S f)
ifThenElseSuccSucc True  t f = Refl
ifThenElseSuccSucc False t f = Refl

total ifThenElsePlusPlusLeft : (cond : Bool) -> (left : Nat) -> (t : Nat) -> (f : Nat) ->
  left + (ifThenElse cond t f) = ifThenElse cond (left + t) (left + f)
ifThenElsePlusPlusLeft True  left t f = Refl
ifThenElsePlusPlusLeft False left t f = Refl

total ifThenElsePlusPlusRight : (cond : Bool) -> (right : Nat) -> (t : Nat) -> (f : Nat) ->
  (ifThenElse cond t f) + right = ifThenElse cond (t + right) (f + right)
ifThenElsePlusPlusRight True  right t f = Refl
ifThenElsePlusPlusRight False right t f = Refl

total ifThenElseMultMultLeft : (cond : Bool) -> (left : Nat) -> (t : Nat) -> (f : Nat) ->
  left * (ifThenElse cond t f) = ifThenElse cond (left * t) (left * f)
ifThenElseMultMultLeft True  left t f = Refl
ifThenElseMultMultLeft False left t f = Refl

total ifThenElseMultMultRight : (cond : Bool) -> (right : Nat) -> (t : Nat) -> (f : Nat) ->
  (ifThenElse cond t f) * right = ifThenElse cond (t * right) (f * right)
ifThenElseMultMultRight True  right t f = Refl
ifThenElseMultMultRight False right t f = Refl

-- Orders
total lteNTrue : (n : Nat) -> lte n n = True
lteNTrue Z     = Refl
lteNTrue (S n) = lteNTrue n

total LTESuccZeroFalse : (n : Nat) -> lte (S n) Z = False
LTESuccZeroFalse Z     = Refl
LTESuccZeroFalse (S n) = Refl

-- Minimum and maximum
total maximumAssociative : (l,c,r : Nat) -> maximum l (maximum c r) = maximum (maximum l c) r
maximumAssociative Z c r = Refl
maximumAssociative (S k) Z r = Refl
maximumAssociative (S k) (S j) Z = Refl
maximumAssociative (S k) (S j) (S i) = rewrite maximumAssociative k j i in Refl

total maximumCommutative : (l, r : Nat) -> maximum l r = maximum r l
maximumCommutative Z Z = Refl
maximumCommutative Z (S k) = Refl
maximumCommutative (S k) Z = Refl
maximumCommutative (S k) (S j) = rewrite maximumCommutative k j in Refl

total maximumIdempotent : (n : Nat) -> maximum n n = n
maximumIdempotent Z = Refl
maximumIdempotent (S k) = cong (maximumIdempotent k)

total minimumAssociative : (l,c,r : Nat) -> minimum l (minimum c r) = minimum (minimum l c) r
minimumAssociative Z c r = Refl
minimumAssociative (S k) Z r = Refl
minimumAssociative (S k) (S j) Z = Refl
minimumAssociative (S k) (S j) (S i) = rewrite minimumAssociative k j i in Refl

total minimumCommutative : (l, r : Nat) -> minimum l r = minimum r l
minimumCommutative Z Z = Refl
minimumCommutative Z (S k) = Refl
minimumCommutative (S k) Z = Refl
minimumCommutative (S k) (S j) = rewrite minimumCommutative k j in Refl

total minimumIdempotent : (n : Nat) -> minimum n n = n
minimumIdempotent Z = Refl
minimumIdempotent (S k) = cong (minimumIdempotent k)

total minimumZeroZeroRight : (right : Nat) -> minimum 0 right = Z
minimumZeroZeroRight Z = Refl
minimumZeroZeroRight (S right) = minimumZeroZeroRight right

total minimumZeroZeroLeft : (left : Nat) -> minimum left 0 = Z
minimumZeroZeroLeft Z        = Refl
minimumZeroZeroLeft (S left) = Refl

total minimumSuccSucc : (left : Nat) -> (right : Nat) ->
  minimum (S left) (S right) = S (minimum left right)
minimumSuccSucc Z        Z         = Refl
minimumSuccSucc (S left) Z         = Refl
minimumSuccSucc Z        (S right) = Refl
minimumSuccSucc (S left) (S right) =
  let inductiveHypothesis = minimumSuccSucc left right in
    ?minimumSuccSuccStepCase

total maximumZeroNRight : (right : Nat) -> maximum Z right = right
maximumZeroNRight Z         = Refl
maximumZeroNRight (S right) = Refl

total maximumZeroNLeft : (left : Nat) -> maximum left Z = left
maximumZeroNLeft Z        = Refl
maximumZeroNLeft (S left) = Refl

total maximumSuccSucc : (left : Nat) -> (right : Nat) ->
  S (maximum left right) = maximum (S left) (S right)
maximumSuccSucc Z        Z         = Refl
maximumSuccSucc (S left) Z         = Refl
maximumSuccSucc Z        (S right) = Refl
maximumSuccSucc (S left) (S right) =
  let inductiveHypothesis = maximumSuccSucc left right in
    ?maximumSuccSuccStepCase

total sucMaxL : (l : Nat) -> maximum (S l) l = (S l)
sucMaxL Z = Refl
sucMaxL (S l) = cong (sucMaxL l)

total sucMaxR : (l : Nat) -> maximum l (S l) = (S l)
sucMaxR Z = Refl
sucMaxR (S l) = cong (sucMaxR l)

total sucMinL : (l : Nat) -> minimum (S l) l = l
sucMinL Z = Refl
sucMinL (S l) = cong (sucMinL l)

total sucMinR : (l : Nat) -> minimum l (S l) = l
sucMinR Z = Refl
sucMinR (S l) = cong (sucMinR l)

--------------------------------------------------------------------------------
-- Proofs
--------------------------------------------------------------------------------

powerPowerMultPowerStepCase = proof {
    intros;
    rewrite sym inductiveHypothesis;
    rewrite sym (multRightSuccPlus exp exp');
    rewrite (multPowerPowerPlus base exp (mult exp exp'));
    trivial;
}

powerPowerMultPowerBaseCase = proof {
    intros;
    rewrite sym (multZeroRightZero exp);
    trivial;
}

powerSuccSuccMultStepCase = proof {
    intros;
    rewrite (multOneRightNeutral base);
    rewrite sym (multOneRightNeutral base);
    trivial;
}

powerOneSuccOneStepCase = proof {
    intros;
    rewrite inductiveHypothesis;
    rewrite sym (plusZeroRightNeutral (power (S Z) exp));
    trivial;
}

powerOneNeutralStepCase = proof {
    intros;
    rewrite inductiveHypothesis;
    trivial;
}

multAssociativeStepCase = proof {
    intros;
    rewrite sym (multDistributesOverPlusLeft centre (mult left centre) right);
    rewrite inductiveHypothesis;
    trivial;
}

minusSuccPredStepCase' = proof {
    intros;
    rewrite sym inductiveHypothesis;
    trivial;
}

minusSuccPredStepCase = proof {
    intros;
    rewrite (minusZeroRight left);
    trivial;
}

multPowerPowerPlusStepCase = proof {
    intros;
    rewrite inductiveHypothesis;
    rewrite (multAssociative base (power base exp) (power base exp'));
    trivial;
}

multPowerPowerPlusBaseCase = proof {
    intros;
    rewrite (plusZeroRightNeutral (power base exp'));
    trivial;
}

multOneRightNeutralStepCase = proof {
    intros;
    rewrite inductiveHypothesis;
    trivial;
}

multOneLeftNeutralStepCase = proof {
    intros;
    rewrite (plusZeroRightNeutral right);
    trivial;
}

multDistributesOverPlusLeftStepCase = proof {
    intros;
    rewrite sym inductiveHypothesis;
    rewrite sym (plusAssociative right (mult left right) (mult centre right));
    trivial;
}

multDistributesOverPlusRightStepCase = proof {
    intros;
    rewrite sym inductiveHypothesis;
    rewrite sym (plusAssociative (plus centre (mult left centre)) right (mult left right));
    rewrite (plusAssociative centre (mult left centre) right);
    rewrite sym (plusCommutative (mult left centre) right);
    rewrite sym (plusAssociative centre right (mult left centre));
    rewrite sym (plusAssociative (plus centre right) (mult left centre) (mult left right));
    trivial;
}

multCommutativeStepCase = proof {
    intros;
    rewrite sym (multRightSuccPlus right left);
    rewrite inductiveHypothesis;
    trivial;
}

multCommutativeBaseCase = proof {
    intros;
    rewrite (multZeroRightZero right);
    trivial;
}

multRightSuccPlusStepCase = proof {
    intros;
    rewrite inductiveHypothesis;
    rewrite sym inductiveHypothesis;
    rewrite sym (plusAssociative right left (mult left right));
    rewrite sym (plusCommutative right left);
    rewrite (plusAssociative left right (mult left right));
    trivial;
}

multZeroRightZeroStepCase = proof {
    intros;
    rewrite inductiveHypothesis;
    trivial;
}

plusAssociativeStepCase = proof {
    intros;
    rewrite inductiveHypothesis;
    trivial;
}

plusCommutativeStepCase = proof {
    intros;
    rewrite (plusSuccRightSucc right left);
    rewrite inductiveHypothesis;
    trivial;
}

plusSuccRightSuccStepCase = proof {
    intros;
    rewrite inductiveHypothesis;
    trivial;
}

plusCommutativeBaseCase = proof {
    intros;
    rewrite sym (plusZeroRightNeutral right);
    trivial;
}

plusZeroRightNeutralStepCase = proof {
    intros;
    rewrite inductiveHypothesis;
    trivial;
}

maximumSuccSuccStepCase = proof {
    intros;
    rewrite sym (ifThenElseSuccSucc (lte left right) (S right) (S left));
    trivial;
}

minimumSuccSuccStepCase = proof {
    intros;
    rewrite (ifThenElseSuccSucc (lte left right) (S left) (S right));
    trivial;
}

multDistributesOverMinusRightBody = proof {
    intros;
    rewrite sym (multCommutative left (minus centre right));
    rewrite sym (multDistributesOverMinusLeft centre right left);
    rewrite sym (multCommutative centre left);
    rewrite sym (multCommutative right left);
    trivial;
}

multDistributesOverMinusLeftStepCase = proof {
    intros;
    rewrite sym (plusMinusLeftCancel right (mult left right) (mult centre right));
    trivial;
}

multDistributesOverMinusLeftBaseCase = proof {
    intros;
    rewrite (minusZeroRight (plus right (mult left right)));
    trivial;
}

plusMinusLeftCancelStepCase = proof {
    intros;
    rewrite inductiveHypothesis;
    trivial;
}

minusMinusMinusPlusStepCase = proof {
    intros;
    rewrite inductiveHypothesis;
    trivial;
}

plusLeftLeftRightZeroBaseCase = proof {
    intros;
    rewrite p;
    trivial;
}

plusLeftLeftRightZeroStepCase = proof {
    intros;
    refine inductiveHypothesis;
    let p' = succInjective (plus left right) left p;
    rewrite p';
    trivial;
}

plusRightCancelStepCase = proof {
    intros;
    refine inductiveHypothesis;
    refine succInjective _ _ ?;
    rewrite sym (plusSuccRightSucc left right);
    rewrite sym (plusSuccRightSucc left' right);
    rewrite p;
    trivial;
}

plusRightCancelBaseCase = proof {
    intros;
    rewrite (plusZeroRightNeutral left);
    rewrite (plusZeroRightNeutral left');
    rewrite p;
    trivial;
}

plusLeftCancelStepCase = proof {
    intros;
    let injectiveProof = succInjective (plus left right) (plus left right') p;
    rewrite (inductiveHypothesis injectiveProof);
    trivial;
}

plusLeftCancelBaseCase = proof {
    intros;
    rewrite p;
    trivial;
}
