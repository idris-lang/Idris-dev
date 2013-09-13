module Prelude.Nat

import Builtins

import Prelude.Algebra
import Prelude.Cast

%access public
%default total

data Nat
  = Z
  | S Nat

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

total plus : Nat -> Nat -> Nat
plus Z right        = right
plus (S left) right = S (plus left right)

total mult : Nat -> Nat -> Nat
mult Z right        = Z
mult (S left) right = plus right $ mult left right

%assert_total
fromIntegerNat : Integer -> Nat
fromIntegerNat 0 = Z
fromIntegerNat n =
  if (n > 0) then
    S (fromIntegerNat (n - 1))
  else
    Z

toIntegerNat : Nat -> Integer
toIntegerNat Z = 0
toIntegerNat (S k) = 1 + toIntegerNat k

total minus : Nat -> Nat -> Nat
minus Z        right     = Z
minus left     Z         = left
minus (S left) (S right) = minus left right

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

data LTE  : Nat -> Nat -> Type where
  lteZero : LTE Z    right
  lteSucc : LTE left right -> LTE (S left) (S right)

total GTE : Nat -> Nat -> Type
GTE left right = LTE right left

total LT : Nat -> Nat -> Type
LT left right = LTE (S left) right

total GT : Nat -> Nat -> Type
GT left right = LT right left

total lte : Nat -> Nat -> Bool
lte Z        right     = True
lte left     Z         = False
lte (S left) (S right) = lte left right

total gte : Nat -> Nat -> Bool
gte left right = lte right left

total lt : Nat -> Nat -> Bool
lt left right = lte (S left) right

total gt : Nat -> Nat -> Bool
gt left right = lt right left

total minimum : Nat -> Nat -> Nat
minimum left right =
  if lte left right then
    left
  else
    right

total maximum : Nat -> Nat -> Nat
maximum left right =
  if lte left right then
    right
  else
    left

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

instance Cast Integer Nat where
  cast = fromInteger

record Multiplicative : Type where
  getMultiplicative : Nat -> Multiplicative

record Additive : Type where
  getAdditive : Nat -> Additive

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

instance MeetSemilattice Nat where
  meet = minimum

instance JoinSemilattice Nat where
  join = maximum

instance Lattice Nat where { }

instance BoundedJoinSemilattice Nat where
  bottom = Z

--------------------------------------------------------------------------------
-- Auxilliary notions
--------------------------------------------------------------------------------

total pred : Nat -> Nat
pred Z     = Z
pred (S n) = n

--------------------------------------------------------------------------------
-- Fibonacci and factorial
--------------------------------------------------------------------------------

total fib : Nat -> Nat
fib Z         = Z
fib (S Z)     = S Z
fib (S (S n)) = fib (S n) + fib n

--------------------------------------------------------------------------------
-- GCD and LCM
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- Division and modulus
--------------------------------------------------------------------------------

total mod : Nat -> Nat -> Nat
mod left Z         = left
mod left (S right) = mod' left left right
  where
    total mod' : Nat -> Nat -> Nat -> Nat
    mod' Z        centre right = centre
    mod' (S left) centre right =
      if lte centre right then
        centre
      else
        mod' left (centre - (S right)) right

total div : Nat -> Nat -> Nat
div left Z         = S left               -- div by zero
div left (S right) = div' left left right
  where
    total div' : Nat -> Nat -> Nat -> Nat
    div' Z        centre right = Z
    div' (S left) centre right =
      if lte centre right then
        Z
      else
        S (div' left (centre - (S right)) right)

%assert_total
log2 : Nat -> Nat
log2 Z = Z
log2 (S Z) = Z
log2 n = S (log2 (n `div` 2))

--------------------------------------------------------------------------------
-- Properties
--------------------------------------------------------------------------------

-- Succ
total eqSucc : (left : Nat) -> (right : Nat) -> (p : left = right) ->
  S left = S right
eqSucc left _ refl = refl

total succInjective : (left : Nat) -> (right : Nat) -> (p : S left = S right) ->
  left = right
succInjective left _ refl = refl

-- Plus
total plusZeroLeftNeutral : (right : Nat) -> 0 + right = right
plusZeroLeftNeutral right = refl

total plusZeroRightNeutral : (left : Nat) -> left + 0 = left
plusZeroRightNeutral Z     = refl
plusZeroRightNeutral (S n) =
  let inductiveHypothesis = plusZeroRightNeutral n in
    ?plusZeroRightNeutralStepCase

total plusSuccRightSucc : (left : Nat) -> (right : Nat) ->
  S (left + right) = left + (S right)
plusSuccRightSucc Z right        = refl
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
plusAssociative Z        centre right = refl
plusAssociative (S left) centre right =
  let inductiveHypothesis = plusAssociative left centre right in
    ?plusAssociativeStepCase

total plusConstantRight : (left : Nat) -> (right : Nat) -> (c : Nat) ->
  (p : left = right) -> left + c = right + c
plusConstantRight left _ c refl = refl

total plusConstantLeft : (left : Nat) -> (right : Nat) -> (c : Nat) ->
  (p : left = right) -> c + left = c + right
plusConstantLeft left _ c refl = refl

total plusOneSucc : (right : Nat) -> 1 + right = S right
plusOneSucc n = refl

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
multZeroLeftZero right = refl

total multZeroRightZero : (left : Nat) -> left * Z = Z
multZeroRightZero Z        = refl
multZeroRightZero (S left) =
  let inductiveHypothesis = multZeroRightZero left in
    ?multZeroRightZeroStepCase

total multRightSuccPlus : (left : Nat) -> (right : Nat) ->
  left * (S right) = left + (left * right)
multRightSuccPlus Z        right = refl
multRightSuccPlus (S left) right =
  let inductiveHypothesis = multRightSuccPlus left right in
    ?multRightSuccPlusStepCase

total multLeftSuccPlus : (left : Nat) -> (right : Nat) ->
  (S left) * right = right + (left * right)
multLeftSuccPlus left right = refl

total multCommutative : (left : Nat) -> (right : Nat) ->
  left * right = right * left
multCommutative Z right        = ?multCommutativeBaseCase
multCommutative (S left) right =
  let inductiveHypothesis = multCommutative left right in
    ?multCommutativeStepCase

total multDistributesOverPlusRight : (left : Nat) -> (centre : Nat) -> (right : Nat) ->
  left * (centre + right) = (left * centre) + (left * right)
multDistributesOverPlusRight Z        centre right = refl
multDistributesOverPlusRight (S left) centre right =
  let inductiveHypothesis = multDistributesOverPlusRight left centre right in
    ?multDistributesOverPlusRightStepCase

total multDistributesOverPlusLeft : (left : Nat) -> (centre : Nat) -> (right : Nat) ->
  (left + centre) * right = (left * right) + (centre * right)
multDistributesOverPlusLeft Z        centre right = refl
multDistributesOverPlusLeft (S left) centre right =
  let inductiveHypothesis = multDistributesOverPlusLeft left centre right in
    ?multDistributesOverPlusLeftStepCase

total multAssociative : (left : Nat) -> (centre : Nat) -> (right : Nat) ->
  left * (centre * right) = (left * centre) * right
multAssociative Z        centre right = refl
multAssociative (S left) centre right =
  let inductiveHypothesis = multAssociative left centre right in
    ?multAssociativeStepCase

total multOneLeftNeutral : (right : Nat) -> 1 * right = right
multOneLeftNeutral Z         = refl
multOneLeftNeutral (S right) =
  let inductiveHypothesis = multOneLeftNeutral right in
    ?multOneLeftNeutralStepCase

total multOneRightNeutral : (left : Nat) -> left * 1 = left
multOneRightNeutral Z        = refl
multOneRightNeutral (S left) =
  let inductiveHypothesis = multOneRightNeutral left in
    ?multOneRightNeutralStepCase

-- Minus
total minusSuccSucc : (left : Nat) -> (right : Nat) ->
  (S left) - (S right) = left - right
minusSuccSucc left right = refl

total minusZeroLeft : (right : Nat) -> 0 - right = Z
minusZeroLeft right = refl

total minusZeroRight : (left : Nat) -> left - 0 = left
minusZeroRight Z        = refl
minusZeroRight (S left) = refl

total minusZeroN : (n : Nat) -> Z = n - n
minusZeroN Z     = refl
minusZeroN (S n) = minusZeroN n

total minusOneSuccN : (n : Nat) -> S Z = (S n) - n
minusOneSuccN Z     = refl
minusOneSuccN (S n) = minusOneSuccN n

total minusSuccOne : (n : Nat) -> S n - 1 = n
minusSuccOne Z     = refl
minusSuccOne (S n) = refl

total minusPlusZero : (n : Nat) -> (m : Nat) -> n - (n + m) = Z
minusPlusZero Z     m = refl
minusPlusZero (S n) m = minusPlusZero n m

total minusMinusMinusPlus : (left : Nat) -> (centre : Nat) -> (right : Nat) ->
  left - centre - right = left - (centre + right)
minusMinusMinusPlus Z        Z          right = refl
minusMinusMinusPlus (S left) Z          right = refl
minusMinusMinusPlus Z        (S centre) right = refl
minusMinusMinusPlus (S left) (S centre) right =
  let inductiveHypothesis = minusMinusMinusPlus left centre right in
    ?minusMinusMinusPlusStepCase

total plusMinusLeftCancel : (left : Nat) -> (right : Nat) -> (right' : Nat) ->
  (left + right) - (left + right') = right - right'
plusMinusLeftCancel Z right right'        = refl
plusMinusLeftCancel (S left) right right' =
  let inductiveHypothesis = plusMinusLeftCancel left right right' in
    ?plusMinusLeftCancelStepCase

total multDistributesOverMinusLeft : (left : Nat) -> (centre : Nat) -> (right : Nat) ->
  (left - centre) * right = (left * right) - (centre * right)
multDistributesOverMinusLeft Z        Z          right = refl
multDistributesOverMinusLeft (S left) Z          right =
  ?multDistributesOverMinusLeftBaseCase
multDistributesOverMinusLeft Z        (S centre) right = refl
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
powerSuccPowerLeft base exp = refl

total multPowerPowerPlus : (base : Nat) -> (exp : Nat) -> (exp' : Nat) ->
  (power base exp) * (power base exp') = power base (exp + exp')
multPowerPowerPlus base Z       exp' = ?multPowerPowerPlusBaseCase
multPowerPowerPlus base (S exp) exp' =
  let inductiveHypothesis = multPowerPowerPlus base exp exp' in
    ?multPowerPowerPlusStepCase

total powerZeroOne : (base : Nat) -> power base 0 = S Z
powerZeroOne base = refl

total powerOneNeutral : (base : Nat) -> power base 1 = base
powerOneNeutral Z        = refl
powerOneNeutral (S base) =
  let inductiveHypothesis = powerOneNeutral base in
    ?powerOneNeutralStepCase

total powerOneSuccOne : (exp : Nat) -> power 1 exp = S Z
powerOneSuccOne Z       = refl
powerOneSuccOne (S exp) =
  let inductiveHypothesis = powerOneSuccOne exp in
    ?powerOneSuccOneStepCase

total powerSuccSuccMult : (base : Nat) -> power base 2 = mult base base
powerSuccSuccMult Z        = refl
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
predSucc n = refl

total minusSuccPred : (left : Nat) -> (right : Nat) ->
  left - (S right) = pred (left - right)
minusSuccPred Z        right = refl
minusSuccPred (S left) Z =
  let inductiveHypothesis = minusSuccPred left Z in
    ?minusSuccPredStepCase
minusSuccPred (S left) (S right) =
  let inductiveHypothesis = minusSuccPred left right in
    ?minusSuccPredStepCase'

-- boolElim
total boolElimSuccSucc : (cond : Bool) -> (t : Nat) -> (f : Nat) ->
  S (boolElim cond t f) = boolElim cond (S t) (S f)
boolElimSuccSucc True  t f = refl
boolElimSuccSucc False t f = refl

total boolElimPlusPlusLeft : (cond : Bool) -> (left : Nat) -> (t : Nat) -> (f : Nat) ->
  left + (boolElim cond t f) = boolElim cond (left + t) (left + f)
boolElimPlusPlusLeft True  left t f = refl
boolElimPlusPlusLeft False left t f = refl

total boolElimPlusPlusRight : (cond : Bool) -> (right : Nat) -> (t : Nat) -> (f : Nat) ->
  (boolElim cond t f) + right = boolElim cond (t + right) (f + right)
boolElimPlusPlusRight True  right t f = refl
boolElimPlusPlusRight False right t f = refl

total boolElimMultMultLeft : (cond : Bool) -> (left : Nat) -> (t : Nat) -> (f : Nat) ->
  left * (boolElim cond t f) = boolElim cond (left * t) (left * f)
boolElimMultMultLeft True  left t f = refl
boolElimMultMultLeft False left t f = refl

total boolElimMultMultRight : (cond : Bool) -> (right : Nat) -> (t : Nat) -> (f : Nat) ->
  (boolElim cond t f) * right = boolElim cond (t * right) (f * right)
boolElimMultMultRight True  right t f = refl
boolElimMultMultRight False right t f = refl

-- Orders
total lteNTrue : (n : Nat) -> lte n n = True
lteNTrue Z     = refl
lteNTrue (S n) = lteNTrue n

total lteSuccZeroFalse : (n : Nat) -> lte (S n) Z = False
lteSuccZeroFalse Z     = refl
lteSuccZeroFalse (S n) = refl

-- Minimum and maximum
total minimumZeroZeroRight : (right : Nat) -> minimum 0 right = Z
minimumZeroZeroRight Z         = refl
minimumZeroZeroRight (S right) = minimumZeroZeroRight right

total minimumZeroZeroLeft : (left : Nat) -> minimum left 0 = Z
minimumZeroZeroLeft Z        = refl
minimumZeroZeroLeft (S left) = refl

total minimumSuccSucc : (left : Nat) -> (right : Nat) ->
  minimum (S left) (S right) = S (minimum left right)
minimumSuccSucc Z        Z         = refl
minimumSuccSucc (S left) Z         = refl
minimumSuccSucc Z        (S right) = refl
minimumSuccSucc (S left) (S right) =
  let inductiveHypothesis = minimumSuccSucc left right in
    ?minimumSuccSuccStepCase

total minimumCommutative : (left : Nat) -> (right : Nat) ->
  minimum left right = minimum right left
minimumCommutative Z        Z         = refl
minimumCommutative Z        (S right) = refl
minimumCommutative (S left) Z         = refl
minimumCommutative (S left) (S right) =
  let inductiveHypothesis = minimumCommutative left right in
    ?minimumCommutativeStepCase

total maximumZeroNRight : (right : Nat) -> maximum Z right = right
maximumZeroNRight Z         = refl
maximumZeroNRight (S right) = refl

total maximumZeroNLeft : (left : Nat) -> maximum left Z = left
maximumZeroNLeft Z        = refl
maximumZeroNLeft (S left) = refl

total maximumSuccSucc : (left : Nat) -> (right : Nat) ->
  S (maximum left right) = maximum (S left) (S right)
maximumSuccSucc Z        Z         = refl
maximumSuccSucc (S left) Z         = refl
maximumSuccSucc Z        (S right) = refl
maximumSuccSucc (S left) (S right) =
  let inductiveHypothesis = maximumSuccSucc left right in
    ?maximumSuccSuccStepCase

total maximumCommutative : (left : Nat) -> (right : Nat) ->
  maximum left right = maximum right left
maximumCommutative Z        Z         = refl
maximumCommutative (S left) Z         = refl
maximumCommutative Z        (S right) = refl
maximumCommutative (S left) (S right) =
  let inductiveHypothesis = maximumCommutative left right in
    ?maximumCommutativeStepCase

-- div and mod
total modZeroZero : (n : Nat) -> mod 0 n = Z
modZeroZero Z     = refl
modZeroZero (S n) = refl

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

maximumCommutativeStepCase = proof {
    intros;
    rewrite (boolElimSuccSucc (lte left right) right left);
    rewrite (boolElimSuccSucc (lte right left) left right);
    rewrite inductiveHypothesis;
    trivial;
}

maximumSuccSuccStepCase = proof {
    intros;
    rewrite sym (boolElimSuccSucc (lte left right) (S right) (S left));
    trivial;
}

minimumCommutativeStepCase = proof {
    intros;
    rewrite (boolElimSuccSucc (lte left right) left right);
    rewrite (boolElimSuccSucc (lte right left) right left);
    rewrite inductiveHypothesis;
    trivial;
}

minimumSuccSuccStepCase = proof {
    intros;
    rewrite (boolElimSuccSucc (lte left right) (S left) (S right));
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
