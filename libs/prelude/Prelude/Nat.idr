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
data Nat =
  ||| Zero
  Z |
  ||| Successor
  S Nat

-- name hints for interactive editing
%name Nat k,j,i,n,m

Uninhabited (Z = S n) where
  uninhabited Refl impossible

Uninhabited (S n = Z) where
  uninhabited Refl impossible

--------------------------------------------------------------------------------
-- Syntactic tests
--------------------------------------------------------------------------------

isZero : Nat -> Bool
isZero Z     = True
isZero (S n) = False

isSucc : Nat -> Bool
isSucc Z     = False
isSucc (S n) = True


||| Proof that `n` is not equal to Z
data IsSucc : (n : Nat) -> Type where
  ItIsSucc : IsSucc (S n)

Uninhabited (IsSucc Z) where
  uninhabited ItIsSucc impossible

||| A decision procedure for `IsSucc`
isItSucc : (n : Nat) -> Dec (IsSucc n)
isItSucc Z = No absurd
isItSucc (S n) = Yes ItIsSucc

--------------------------------------------------------------------------------
-- Basic arithmetic functions
--------------------------------------------------------------------------------

||| Add two natural numbers.
||| @ n the number to case-split on
||| @ m the other number
plus : (n, m : Nat) -> Nat
plus Z right        = right
plus (S left) right = S (plus left right)

||| Multiply natural numbers
mult : Nat -> Nat -> Nat
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
minus : Nat -> Nat -> Nat
minus Z        right     = Z
minus left     Z         = left
minus (S left) (S right) = minus left right

||| Exponentiation of natural numbers
power : Nat -> Nat -> Nat
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
GTE : Nat -> Nat -> Type
GTE left right = LTE right left

||| Strict less than
LT : Nat -> Nat -> Type
LT left right = LTE (S left) right

||| Strict greater than
GT : Nat -> Nat -> Type
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

||| If a number is not less than another, it is greater than or equal to it
notLTImpliesGTE : Not (LT a b) -> GTE a b
notLTImpliesGTE {b = Z} _ = LTEZero
notLTImpliesGTE {a = Z} {b = S k} notLt = absurd (notLt (LTESucc LTEZero))
notLTImpliesGTE {a = S k} {b = S j} notLt = LTESucc (notLTImpliesGTE (notLt . LTESucc))

||| Boolean test than one Nat is less than or equal to another
lte : Nat -> Nat -> Bool
lte Z        right     = True
lte left     Z         = False
lte (S left) (S right) = lte left right

||| Boolean test than one Nat is greater than or equal to another
gte : Nat -> Nat -> Bool
gte left right = lte right left

||| Boolean test than one Nat is strictly less than another
lt : Nat -> Nat -> Bool
lt left right = lte (S left) right

||| Boolean test than one Nat is strictly greater than another
gt : Nat -> Nat -> Bool
gt left right = lt right left

||| Find the least of two natural numbers
minimum : Nat -> Nat -> Nat
minimum Z m = Z
minimum (S n) Z = Z
minimum (S n) (S m) = S (minimum n m)

||| Find the greatest of two natural numbers
maximum : Nat -> Nat -> Nat
maximum Z m = m
maximum (S n) Z = S n
maximum (S n) (S m) = S (maximum n m)

||| Cast Nat to Int
||| Note that this can overflow
toIntNat : Nat -> Int
toIntNat n = prim__truncBigInt_Int (toIntegerNat n)

(-) : (m, n : Nat) -> {auto smaller : LTE n m} -> Nat
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

Abs Nat where
  abs = id

MinBound Nat where
  minBound = Z

||| Casts negative `Integers` to 0.
Cast Integer Nat where
  cast = fromInteger

Cast String Nat where
  cast str = cast (the Integer (cast str))

Cast Nat String where
  cast n = cast (the Integer (cast n))

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
pred : Nat -> Nat
pred Z     = Z
pred (S n) = n

--------------------------------------------------------------------------------
-- Fibonacci and factorial
--------------------------------------------------------------------------------

||| Fibonacci numbers
fib : Nat -> Nat
fib Z         = Z
fib (S Z)     = S Z
fib (S (S n)) = fib (S n) + fib n

||| Factorial function
fact : Nat -> Nat
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
gcd : (a, b : Nat) -> .{auto ok: NotBothZero a b} -> Nat
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

cmp : (x, y : Nat) -> CmpNat x y
cmp Z Z     = CmpEQ
cmp Z (S _) = CmpLT _
cmp (S _) Z = CmpGT _
cmp (S x) (S y) with (cmp x y)
  cmp (S x) (S (x + (S k))) | CmpLT k = CmpLT k
  cmp (S x) (S x)           | CmpEQ   = CmpEQ
  cmp (S (y + (S k))) (S y) | CmpGT k = CmpGT k

--------------------------------------------------------------------------------
-- Properties
--------------------------------------------------------------------------------

-- Succ

||| S preserves equality
eqSucc : (left, right : Nat) -> left = right -> S left = S right
eqSucc _ _ Refl = Refl

||| S is injective
succInjective : (left, right : Nat) -> S left = S right -> left = right
succInjective _ _ Refl = Refl

-- Plus
plusZeroLeftNeutral : (right : Nat) -> 0 + right = right
plusZeroLeftNeutral right = Refl

plusZeroRightNeutral : (left : Nat) -> left + 0 = left
plusZeroRightNeutral Z     = Refl
plusZeroRightNeutral (S n) = rewrite plusZeroRightNeutral n in Refl

plusSuccRightSucc : (left, right : Nat) -> S (left + right) = left + (S right)
plusSuccRightSucc Z _ = Refl
plusSuccRightSucc (S left) right = rewrite plusSuccRightSucc left right in Refl

plusCommutative : (left, right : Nat) -> left + right = right + left
plusCommutative Z right = rewrite plusZeroRightNeutral right in Refl
plusCommutative (S left) right =
  rewrite plusCommutative left right in
    rewrite plusSuccRightSucc right left in
      Refl

plusAssociative : (left, centre, right : Nat) ->
  left + (centre + right) = (left + centre) + right
plusAssociative Z _ _ = Refl
plusAssociative (S left) centre right =
    rewrite plusAssociative left centre right in Refl

plusConstantRight : (left, right, c : Nat) -> left = right ->
  left + c = right + c
plusConstantRight _ _ _ Refl = Refl

plusConstantLeft : (left, right, c : Nat) -> left = right ->
  c + left = c + right
plusConstantLeft _ _ _ Refl = Refl

plusOneSucc : (right : Nat) -> 1 + right = S right
plusOneSucc _ = Refl

plusLeftCancel : (left, right, right' : Nat) ->
  left + right = left + right' -> right = right'
plusLeftCancel Z _ _ p = p
plusLeftCancel (S left) right right' p =
    plusLeftCancel left right right' (succInjective _ _ p)

plusRightCancel : (left, left', right : Nat) ->
  left + right = left' + right -> left = left'
plusRightCancel left left' right p =
  plusLeftCancel right left left' $
    rewrite plusCommutative right left in
      rewrite plusCommutative right left' in
        p

plusLeftLeftRightZero : (left, right : Nat) ->
  left + right = left -> right = Z
plusLeftLeftRightZero left right p =
  plusLeftCancel left right Z $
    rewrite plusZeroRightNeutral left in
      p

-- Mult
multZeroLeftZero : (right : Nat) -> Z * right = Z
multZeroLeftZero _ = Refl

multZeroRightZero : (left : Nat) -> left * Z = Z
multZeroRightZero Z        = Refl
multZeroRightZero (S left) = multZeroRightZero left

multRightSuccPlus : (left, right : Nat) ->
  left * (S right) = left + (left * right)
multRightSuccPlus Z _ = Refl
multRightSuccPlus (S left) right =
  rewrite multRightSuccPlus left right in
  rewrite plusAssociative left right (left * right) in
  rewrite plusAssociative right left (left * right) in
  rewrite plusCommutative right left in
          Refl

multLeftSuccPlus : (left, right : Nat) ->
  (S left) * right = right + (left * right)
multLeftSuccPlus _ _ = Refl

multCommutative : (left, right : Nat) -> left * right = right * left
multCommutative Z right = rewrite multZeroRightZero right in Refl
multCommutative (S left) right =
  rewrite multCommutative left right in
  rewrite multRightSuccPlus right left in
          Refl

multDistributesOverPlusLeft : (left, centre, right : Nat) ->
  (left + centre) * right = (left * right) + (centre * right)
multDistributesOverPlusLeft Z _ _ = Refl
multDistributesOverPlusLeft (S k) centre right =
  rewrite multDistributesOverPlusLeft k centre right in
    rewrite plusAssociative right (k * right) (centre * right) in
      Refl

multDistributesOverPlusRight : (left, centre, right : Nat) ->
  left * (centre + right) = (left * centre) + (left * right)
multDistributesOverPlusRight left centre right =
  rewrite multCommutative left (centre + right) in
    rewrite multCommutative left centre in
      rewrite multCommutative left right in
  multDistributesOverPlusLeft centre right left

multAssociative : (left, centre, right : Nat) ->
  left * (centre * right) = (left * centre) * right
multAssociative Z _ _ = Refl
multAssociative (S left) centre right =
  let inductiveHypothesis = multAssociative left centre right in
    rewrite inductiveHypothesis in
    rewrite multDistributesOverPlusLeft centre (mult left centre) right in
            Refl

multOneLeftNeutral : (right : Nat) -> 1 * right = right
multOneLeftNeutral right = plusZeroRightNeutral right

multOneRightNeutral : (left : Nat) -> left * 1 = left
multOneRightNeutral left = rewrite multCommutative left 1 in multOneLeftNeutral left

-- Minus
minusSuccSucc : (left, right : Nat) ->
  minus (S left) (S right) = minus left right
minusSuccSucc _ _ = Refl

minusZeroLeft : (right : Nat) -> minus 0 right = Z
minusZeroLeft _ = Refl

minusZeroRight : (left : Nat) -> minus left 0 = left
minusZeroRight Z     = Refl
minusZeroRight (S _) = Refl

minusZeroN : (n : Nat) -> Z = minus n n
minusZeroN Z     = Refl
minusZeroN (S n) = minusZeroN n

minusOneSuccN : (n : Nat) -> S Z = minus (S n) n
minusOneSuccN Z     = Refl
minusOneSuccN (S n) = minusOneSuccN n

minusSuccOne : (n : Nat) -> minus (S n) 1 = n
minusSuccOne Z     = Refl
minusSuccOne (S _) = Refl

minusPlusZero : (n, m : Nat) -> minus n (n + m) = Z
minusPlusZero Z     _ = Refl
minusPlusZero (S n) m = minusPlusZero n m

minusMinusMinusPlus : (left, centre, right : Nat) ->
  minus (minus left centre) right = minus left (centre + right)
minusMinusMinusPlus Z Z _ = Refl
minusMinusMinusPlus (S _) Z _ = Refl
minusMinusMinusPlus Z (S _) _ = Refl
minusMinusMinusPlus (S left) (S centre) right =
  rewrite minusMinusMinusPlus left centre right in Refl

plusMinusLeftCancel : (left, right : Nat) -> (right' : Nat) ->
  minus (left + right) (left + right') = minus right right'
plusMinusLeftCancel Z _ _ = Refl
plusMinusLeftCancel (S left) right right' =
  rewrite plusMinusLeftCancel left right right' in Refl

multDistributesOverMinusLeft : (left, centre, right : Nat) ->
  (minus left centre) * right = minus (left * right) (centre * right)
multDistributesOverMinusLeft Z Z _ = Refl
multDistributesOverMinusLeft (S left) Z right =
  rewrite minusZeroRight (right + (left * right)) in Refl
multDistributesOverMinusLeft Z (S _) _ = Refl
multDistributesOverMinusLeft (S left) (S centre) right =
  rewrite multDistributesOverMinusLeft left centre right in
  rewrite plusMinusLeftCancel right (left * right) (centre * right) in
          Refl

multDistributesOverMinusRight : (left, centre, right : Nat) ->
  left * (minus centre right) = minus (left * centre) (left * right)
multDistributesOverMinusRight left centre right =
    rewrite multCommutative left (minus centre right) in
    rewrite multDistributesOverMinusLeft centre right left in
    rewrite multCommutative centre left in
    rewrite multCommutative right left in
            Refl

-- Power
powerSuccPowerLeft : (base, exp : Nat) -> power base (S exp) =
  base * (power base exp)
powerSuccPowerLeft _ _ = Refl

multPowerPowerPlus : (base, exp : Nat) -> (exp' : Nat) ->
  (power base exp) * (power base exp') = power base (exp + exp')
multPowerPowerPlus base Z       exp' =
    rewrite sym $ plusZeroRightNeutral (power base exp') in Refl
multPowerPowerPlus base (S exp) exp' =
  let inductiveHypothesis = multPowerPowerPlus base exp exp' in
    rewrite sym inductiveHypothesis in
    rewrite sym (multAssociative base (power base exp) (power base exp')) in
            Refl

powerZeroOne : (base : Nat) -> power base 0 = S Z
powerZeroOne _ = Refl

powerOneNeutral : (base : Nat) -> power base 1 = base
powerOneNeutral base = rewrite multCommutative base 1 in multOneLeftNeutral base

powerOneSuccOne : (exp : Nat) -> power 1 exp = S Z
powerOneSuccOne Z       = Refl
powerOneSuccOne (S exp) = rewrite powerOneSuccOne exp in Refl

powerSuccSuccMult : (base : Nat) -> power base 2 = mult base base
powerSuccSuccMult base = rewrite multOneRightNeutral base in Refl

powerPowerMultPower : (base, exp : Nat) -> (exp' : Nat) ->
  power (power base exp) exp' = power base (exp * exp')
powerPowerMultPower _ exp Z = rewrite multZeroRightZero exp in Refl
powerPowerMultPower base exp (S exp') =
  rewrite powerPowerMultPower base exp exp' in
  rewrite multRightSuccPlus exp exp' in
  rewrite sym $ multPowerPowerPlus base exp (exp * exp') in
          Refl

-- Pred
predSucc : (n : Nat) -> pred (S n) = n
predSucc _ = Refl

minusSuccPred : (left, right : Nat) ->
  minus left (S right) = pred (minus left right)
minusSuccPred Z _ = Refl
minusSuccPred (S left) Z = rewrite minusZeroRight left in Refl
minusSuccPred (S left) (S right) = rewrite minusSuccPred left right in Refl

-- ifThenElse
ifThenElseSuccSucc : (cond : Bool) -> (t, f : Nat) ->
  S (ifThenElse cond t f) = ifThenElse cond (S t) (S f)
ifThenElseSuccSucc True  _ _ = Refl
ifThenElseSuccSucc False _ _ = Refl

ifThenElsePlusPlusLeft : (cond : Bool) -> (left, t, f : Nat) ->
  left + (ifThenElse cond t f) = ifThenElse cond (left + t) (left + f)
ifThenElsePlusPlusLeft True  _ _ _ = Refl
ifThenElsePlusPlusLeft False _ _ _ = Refl

ifThenElsePlusPlusRight : (cond : Bool) -> (right, t, f : Nat) ->
  (ifThenElse cond t f) + right = ifThenElse cond (t + right) (f + right)
ifThenElsePlusPlusRight True  _ _ _ = Refl
ifThenElsePlusPlusRight False _ _ _ = Refl

ifThenElseMultMultLeft : (cond : Bool) -> (left, t, f : Nat) ->
  left * (ifThenElse cond t f) = ifThenElse cond (left * t) (left * f)
ifThenElseMultMultLeft True  _ _ _ = Refl
ifThenElseMultMultLeft False _ _ _ = Refl

ifThenElseMultMultRight : (cond : Bool) -> (right, t, f : Nat) ->
  (ifThenElse cond t f) * right = ifThenElse cond (t * right) (f * right)
ifThenElseMultMultRight True  _ _ _ = Refl
ifThenElseMultMultRight False _ _ _ = Refl

-- Orders
lteNTrue : (n : Nat) -> lte n n = True
lteNTrue Z     = Refl
lteNTrue (S n) = lteNTrue n

LTESuccZeroFalse : (n : Nat) -> lte (S n) Z = False
LTESuccZeroFalse Z     = Refl
LTESuccZeroFalse (S n) = Refl

-- Minimum and maximum
maximumAssociative : (l,c,r : Nat) -> maximum l (maximum c r) = maximum (maximum l c) r
maximumAssociative Z _ _ = Refl
maximumAssociative (S _) Z _ = Refl
maximumAssociative (S _) (S _) Z = Refl
maximumAssociative (S k) (S j) (S i) = rewrite maximumAssociative k j i in Refl

maximumCommutative : (l, r : Nat) -> maximum l r = maximum r l
maximumCommutative Z Z = Refl
maximumCommutative Z (S _) = Refl
maximumCommutative (S _) Z = Refl
maximumCommutative (S k) (S j) = rewrite maximumCommutative k j in Refl

maximumIdempotent : (n : Nat) -> maximum n n = n
maximumIdempotent Z = Refl
maximumIdempotent (S k) = cong $ maximumIdempotent k

minimumAssociative : (l,c,r : Nat) -> minimum l (minimum c r) = minimum (minimum l c) r
minimumAssociative Z _ _ = Refl
minimumAssociative (S _) Z _ = Refl
minimumAssociative (S _) (S _) Z = Refl
minimumAssociative (S k) (S j) (S i) = rewrite minimumAssociative k j i in Refl

minimumCommutative : (l, r : Nat) -> minimum l r = minimum r l
minimumCommutative Z Z = Refl
minimumCommutative Z (S _) = Refl
minimumCommutative (S _) Z = Refl
minimumCommutative (S k) (S j) = rewrite minimumCommutative k j in Refl

minimumIdempotent : (n : Nat) -> minimum n n = n
minimumIdempotent Z = Refl
minimumIdempotent (S k) = cong (minimumIdempotent k)

minimumZeroZeroRight : (right : Nat) -> minimum 0 right = Z
minimumZeroZeroRight _ = Refl

minimumZeroZeroLeft : (left : Nat) -> minimum left 0 = Z
minimumZeroZeroLeft left = rewrite minimumCommutative left 0 in Refl

minimumSuccSucc : (left, right : Nat) ->
  minimum (S left) (S right) = S (minimum left right)
minimumSuccSucc _ _ = Refl

maximumZeroNRight : (right : Nat) -> maximum Z right = right
maximumZeroNRight right = Refl

maximumZeroNLeft : (left : Nat) -> maximum left Z = left
maximumZeroNLeft left = rewrite maximumCommutative left Z in Refl

maximumSuccSucc : (left, right : Nat) ->
  S (maximum left right) = maximum (S left) (S right)
maximumSuccSucc _ _ = Refl

sucMaxL : (l : Nat) -> maximum (S l) l = (S l)
sucMaxL Z = Refl
sucMaxL (S l) = cong $ sucMaxL l

sucMaxR : (l : Nat) -> maximum l (S l) = (S l)
sucMaxR Z = Refl
sucMaxR (S l) = cong $ sucMaxR l

sucMinL : (l : Nat) -> minimum (S l) l = l
sucMinL Z = Refl
sucMinL (S l) = cong $ sucMinL l

sucMinR : (l : Nat) -> minimum l (S l) = l
sucMinR Z = Refl
sucMinR (S l) = cong $ sucMinR l
