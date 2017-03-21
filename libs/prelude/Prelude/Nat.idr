module Prelude.Nat

import Builtins

import Prelude.Algebra
import Prelude.Basics
import Prelude.Bool
import Prelude.Cast
import Prelude.Interfaces
import Prelude.Uninhabited

%access public export
%default total

||| Natural numbers: unbounded, unsigned integers which can be pattern
||| matched.
%elim data Nat =
  ||| Zero
  Z |
  ||| Successor
  S Nat

-- name hints for interactive editing
%name Nat k,j,i,n,m

Uninhabited (Z = S n) where
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

||| Proofs that `n` or `m` is not equal to Z
data NotBothZero : (n, m : Nat) -> Type where
  LeftIsNotZero  : NotBothZero (S n) m
  RightIsNotZero : NotBothZero n     (S m)


||| Proofs that `n` is less than or equal to `m`
||| @ n the smaller number
||| @ m the larger number
data LTE  : (n, m : Nat) -> Type where
  ||| Zero is the smallest Nat
  LTEZero : LTE Z    right
  ||| If n <= m, then n + 1 <= m + 1
  LTESucc : LTE left right -> LTE (S left) (S right)

Uninhabited (LTE (S n) Z) where
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

||| n + 1 < m implies n < m 
lteSuccLeft : LTE (S n) m -> LTE n m
lteSuccLeft (LTESucc x) = lteSuccRight x

||| `LTE` is transitive
lteTransitive : LTE n m -> LTE m p -> LTE n p
lteTransitive LTEZero y = LTEZero
lteTransitive (LTESucc x) (LTESucc y) = LTESucc (lteTransitive x y)

lteAddRight : (n : Nat) -> LTE n (plus n m)
lteAddRight Z = LTEZero
lteAddRight (S k) = LTESucc (lteAddRight k)


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

(-) : (m : Nat) -> (n : Nat) -> {auto smaller : LTE n m} -> Nat
(-) m n {smaller} = minus m n

--------------------------------------------------------------------------------
-- Interface implementations
--------------------------------------------------------------------------------

Eq Nat where
  Z == Z         = True
  (S l) == (S r) = l == r
  _ == _         = False

Cast Nat Integer where
  cast = toIntegerNat

Ord Nat where
  compare Z Z         = EQ
  compare Z (S k)     = LT
  compare (S k) Z     = GT
  compare (S x) (S y) = compare x y

Num Nat where
  (+) = plus
  (*) = mult

  fromInteger = fromIntegerNat

MinBound Nat where
  minBound = Z

||| Casts negative `Integers` to 0.
Cast Integer Nat where
  cast = fromInteger

Cast String Nat where
    cast str = cast (the Integer (cast str))

||| A wrapper for Nat that specifies the semigroup and monoid implementations that use (*)
record Multiplicative where
  constructor GetMultiplicative
  _ : Nat

||| A wrapper for Nat that specifies the semigroup and monoid implementations that use (+)
record Additive where
  constructor GetAdditive
  _ : Nat

Semigroup Multiplicative where
  (<+>) left right = GetMultiplicative $ left' * right'
    where
      left'  : Nat
      left'  =
       case left of
          GetMultiplicative m => m

      right' : Nat
      right' =
        case right of
          GetMultiplicative m => m

Semigroup Additive where
  left <+> right = GetAdditive $ left' + right'
    where
      left'  : Nat
      left'  =
        case left of
          GetAdditive m => m

      right' : Nat
      right' =
        case right of
          GetAdditive m => m

Monoid Multiplicative where
  neutral = GetMultiplicative $ S Z

Monoid Additive where
  neutral = GetAdditive Z

||| Casts negative `Ints` to 0.
Cast Int Nat where
  cast i = fromInteger (cast i)

Cast Nat Int where
  cast = toIntNat

Cast Nat Double where
  cast = cast . toIntegerNat

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

||| The proof that no successor of a natural number can be zero.
|||
||| ```idris example
||| modNatNZ 10 3 SIsNotZ
||| ```
SIsNotZ : {x: Nat} -> (S x = Z) -> Void
SIsNotZ Refl impossible

||| Modulus function where the divisor is not zero.
|||
||| ```idris example
||| modNatNZ 100 2 SIsNotZ
||| ```
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
        mod' left (minus centre (S right)) right

partial
modNat : Nat -> Nat -> Nat
modNat left (S right) = modNatNZ left (S right) SIsNotZ

||| Division where the divisor is not zero.
|||
||| ```idris example
||| divNatNZ 100 2 SIsNotZ
||| ```
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
        S (div' left (minus centre (S right)) right)

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

partial
Integral Nat where
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
gcd : (a: Nat) -> (b: Nat) -> .{auto ok: NotBothZero a b} -> Nat
gcd a Z     = a
gcd Z b     = b
gcd a (S b) = assert_total $ gcd (S b) (modNatNZ a (S b) SIsNotZ)

lcm : Nat -> Nat -> Nat
lcm _ Z     = Z
lcm Z _     = Z
lcm a (S b) = assert_total $ divNat (a * (S b)) (gcd a (S b))


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
    rewrite inductiveHypothesis in Refl

total plusSuccRightSucc : (left : Nat) -> (right : Nat) ->
  S (left + right) = left + (S right)
plusSuccRightSucc Z right        = Refl
plusSuccRightSucc (S left) right =
  let inductiveHypothesis = plusSuccRightSucc left right in
    rewrite inductiveHypothesis in Refl

total plusCommutative : (left : Nat) -> (right : Nat) ->
  left + right = right + left
plusCommutative Z        right = rewrite plusZeroRightNeutral right in Refl
plusCommutative (S left) right =
  let inductiveHypothesis = plusCommutative left right in
    rewrite inductiveHypothesis in
      rewrite plusSuccRightSucc right left in Refl

total plusAssociative : (left : Nat) -> (centre : Nat) -> (right : Nat) ->
  left + (centre + right) = (left + centre) + right
plusAssociative Z        centre right = Refl
plusAssociative (S left) centre right =
  let inductiveHypothesis = plusAssociative left centre right in
    rewrite inductiveHypothesis in Refl

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
plusLeftCancel Z        right right' p = p
plusLeftCancel (S left) right right' p =
  let inductiveHypothesis = plusLeftCancel left right right' in
    inductiveHypothesis (succInjective _ _ p)

total plusRightCancel : (left : Nat) -> (left' : Nat) -> (right : Nat) ->
  (p : left + right = left' + right) -> left = left'
plusRightCancel left left' Z         p = rewrite sym (plusZeroRightNeutral left) in
                                         rewrite sym (plusZeroRightNeutral left') in
                                                 p
plusRightCancel left left' (S right) p =
  plusRightCancel left left' right
    (succInjective _ _ (rewrite plusSuccRightSucc left right in
                        rewrite plusSuccRightSucc left' right in p))

total plusLeftLeftRightZero : (left : Nat) -> (right : Nat) ->
  (p : left + right = left) -> right = Z
plusLeftLeftRightZero Z        right p = p
plusLeftLeftRightZero (S left) right p =
  plusLeftLeftRightZero left right (succInjective _ _ p)

-- Mult
total multZeroLeftZero : (right : Nat) -> Z * right = Z
multZeroLeftZero right = Refl

total multZeroRightZero : (left : Nat) -> left * Z = Z
multZeroRightZero Z        = Refl
multZeroRightZero (S left) = multZeroRightZero left

total multRightSuccPlus : (left : Nat) -> (right : Nat) ->
  left * (S right) = left + (left * right)
multRightSuccPlus Z        right = Refl
multRightSuccPlus (S left) right =
  let inductiveHypothesis = multRightSuccPlus left right in
    rewrite inductiveHypothesis in
    rewrite plusAssociative left right (mult left right) in
    rewrite plusAssociative right left (mult left right) in
    rewrite plusCommutative right left in
            Refl

total multLeftSuccPlus : (left : Nat) -> (right : Nat) ->
  (S left) * right = right + (left * right)
multLeftSuccPlus left right = Refl

total multCommutative : (left : Nat) -> (right : Nat) ->
  left * right = right * left
multCommutative Z right        = rewrite multZeroRightZero right in Refl
multCommutative (S left) right =
  let inductiveHypothesis = multCommutative left right in
      rewrite inductiveHypothesis in
      rewrite multRightSuccPlus right left in
              Refl

total multDistributesOverPlusRight : (left : Nat) -> (centre : Nat) -> (right : Nat) ->
  left * (centre + right) = (left * centre) + (left * right)
multDistributesOverPlusRight Z        centre right = Refl
multDistributesOverPlusRight (S left) centre right =
  let inductiveHypothesis = multDistributesOverPlusRight left centre right in
    rewrite inductiveHypothesis in
    rewrite plusAssociative (plus centre (mult left centre)) right (mult left right) in
    rewrite sym (plusAssociative centre (mult left centre) right) in
    rewrite plusCommutative (mult left centre) right in
    rewrite plusAssociative centre right (mult left centre) in
    rewrite plusAssociative (plus centre right) (mult left centre) (mult left right) in
            Refl

total multDistributesOverPlusLeft : (left : Nat) -> (centre : Nat) -> (right : Nat) ->
  (left + centre) * right = (left * right) + (centre * right)
multDistributesOverPlusLeft Z        centre right = Refl
multDistributesOverPlusLeft (S left) centre right =
  let inductiveHypothesis = multDistributesOverPlusLeft left centre right in
    rewrite inductiveHypothesis in
    rewrite plusAssociative right (mult left right) (mult centre right) in
            Refl

total multAssociative : (left : Nat) -> (centre : Nat) -> (right : Nat) ->
  left * (centre * right) = (left * centre) * right
multAssociative Z        centre right = Refl
multAssociative (S left) centre right =
  let inductiveHypothesis = multAssociative left centre right in
    rewrite inductiveHypothesis in
    rewrite multDistributesOverPlusLeft centre (mult left centre) right in
            Refl

total multOneLeftNeutral : (right : Nat) -> 1 * right = right
multOneLeftNeutral Z         = Refl
multOneLeftNeutral (S right) =
  let inductiveHypothesis = multOneLeftNeutral right in
    rewrite inductiveHypothesis in
            Refl

total multOneRightNeutral : (left : Nat) -> left * 1 = left
multOneRightNeutral Z        = Refl
multOneRightNeutral (S left) =
  let inductiveHypothesis = multOneRightNeutral left in
    rewrite inductiveHypothesis in
            Refl

-- Minus
total minusSuccSucc : (left : Nat) -> (right : Nat) ->
  minus (S left) (S right) = minus left right
minusSuccSucc left right = Refl

total minusZeroLeft : (right : Nat) -> minus 0 right = Z
minusZeroLeft right = Refl

total minusZeroRight : (left : Nat) -> minus left 0 = left
minusZeroRight Z        = Refl
minusZeroRight (S left) = Refl

total minusZeroN : (n : Nat) -> Z = minus n n
minusZeroN Z     = Refl
minusZeroN (S n) = minusZeroN n

total minusOneSuccN : (n : Nat) -> S Z = minus (S n) n
minusOneSuccN Z     = Refl
minusOneSuccN (S n) = minusOneSuccN n

total minusSuccOne : (n : Nat) -> minus (S n) 1 = n
minusSuccOne Z     = Refl
minusSuccOne (S n) = Refl

total minusPlusZero : (n : Nat) -> (m : Nat) -> minus n (n + m) = Z
minusPlusZero Z     m = Refl
minusPlusZero (S n) m = minusPlusZero n m

total minusMinusMinusPlus : (left : Nat) -> (centre : Nat) -> (right : Nat) ->
  minus (minus left centre) right = minus left (centre + right)
minusMinusMinusPlus Z        Z          right = Refl
minusMinusMinusPlus (S left) Z          right = Refl
minusMinusMinusPlus Z        (S centre) right = Refl
minusMinusMinusPlus (S left) (S centre) right =
  let inductiveHypothesis = minusMinusMinusPlus left centre right in
    rewrite inductiveHypothesis in
            Refl

total plusMinusLeftCancel : (left : Nat) -> (right : Nat) -> (right' : Nat) ->
  minus (left + right) (left + right') = minus right right'
plusMinusLeftCancel Z right right'        = Refl
plusMinusLeftCancel (S left) right right' =
  let inductiveHypothesis = plusMinusLeftCancel left right right' in
    rewrite inductiveHypothesis in
            Refl

total multDistributesOverMinusLeft : (left : Nat) -> (centre : Nat) -> (right : Nat) ->
  (minus left centre) * right = minus (left * right) (centre * right)
multDistributesOverMinusLeft Z        Z          right = Refl
multDistributesOverMinusLeft (S left) Z          right =
    rewrite (minusZeroRight (plus right (mult left right))) in Refl
multDistributesOverMinusLeft Z        (S centre) right = Refl
multDistributesOverMinusLeft (S left) (S centre) right =
  let inductiveHypothesis = multDistributesOverMinusLeft left centre right in
    rewrite inductiveHypothesis in
    rewrite plusMinusLeftCancel right (mult left right) (mult centre right) in
            Refl

total multDistributesOverMinusRight : (left : Nat) -> (centre : Nat) -> (right : Nat) ->
  left * (minus centre right) = minus (left * centre) (left * right)
multDistributesOverMinusRight left centre right =
    rewrite multCommutative left (minus centre right) in
    rewrite multDistributesOverMinusLeft centre right left in
    rewrite multCommutative centre left in
    rewrite multCommutative right left in
            Refl

-- Power
total powerSuccPowerLeft : (base : Nat) -> (exp : Nat) -> power base (S exp) =
  base * (power base exp)
powerSuccPowerLeft base exp = Refl

total multPowerPowerPlus : (base : Nat) -> (exp : Nat) -> (exp' : Nat) ->
  (power base exp) * (power base exp') = power base (exp + exp')
multPowerPowerPlus base Z       exp' =
    rewrite sym (plusZeroRightNeutral (power base exp')) in Refl
multPowerPowerPlus base (S exp) exp' =
  let inductiveHypothesis = multPowerPowerPlus base exp exp' in
    rewrite sym inductiveHypothesis in
    rewrite sym (multAssociative base (power base exp) (power base exp')) in
            Refl

total powerZeroOne : (base : Nat) -> power base 0 = S Z
powerZeroOne base = Refl

total powerOneNeutral : (base : Nat) -> power base 1 = base
powerOneNeutral Z        = Refl
powerOneNeutral (S base) =
  let inductiveHypothesis = powerOneNeutral base in
    rewrite inductiveHypothesis in Refl

total powerOneSuccOne : (exp : Nat) -> power 1 exp = S Z
powerOneSuccOne Z       = Refl
powerOneSuccOne (S exp) =
  let inductiveHypothesis = powerOneSuccOne exp in
    rewrite inductiveHypothesis in Refl

total powerSuccSuccMult : (base : Nat) -> power base 2 = mult base base
powerSuccSuccMult Z        = Refl
powerSuccSuccMult (S base) = rewrite multOneRightNeutral base in Refl

total powerPowerMultPower : (base : Nat) -> (exp : Nat) -> (exp' : Nat) ->
  power (power base exp) exp' = power base (exp * exp')
powerPowerMultPower base exp Z        = rewrite multZeroRightZero exp in Refl
powerPowerMultPower base exp (S exp') =
  let inductiveHypothesis = powerPowerMultPower base exp exp' in
    rewrite inductiveHypothesis in
    rewrite multRightSuccPlus exp exp' in
    rewrite sym (multPowerPowerPlus base exp (mult exp exp')) in
            Refl

-- Pred
total predSucc : (n : Nat) -> pred (S n) = n
predSucc n = Refl

total minusSuccPred : (left : Nat) -> (right : Nat) ->
  minus left (S right) = pred (minus left right)
minusSuccPred Z        right = Refl
minusSuccPred (S left) Z =
    rewrite minusZeroRight left in Refl
minusSuccPred (S left) (S right) =
  let inductiveHypothesis = minusSuccPred left right in
    rewrite inductiveHypothesis in Refl

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
minimumSuccSucc (S left) (S right) = Refl

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
maximumSuccSucc (S left) (S right) = Refl

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
