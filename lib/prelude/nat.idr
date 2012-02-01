module prelude.nat

import builtins

import prelude.algebra
import prelude.cast

%access public

data Nat
  = O
  | S Nat

--------------------------------------------------------------------------------
-- Syntactic tests
--------------------------------------------------------------------------------

isZero : Nat -> Bool
isZero O     = True
isZero (S n) = False

isSucc : Nat -> Bool
isSucc O     = False
isSucc (S n) = True

--------------------------------------------------------------------------------
-- Basic arithmetic functions
--------------------------------------------------------------------------------

plus : Nat -> Nat -> Nat
plus O right        = right
plus (S left) right = S (plus left right)

mult : Nat -> Nat -> Nat
mult O right        = O
mult (S left) right = plus right $ mult left right

minus : Nat -> Nat -> Nat
minus O        right     = O
minus left     O         = left
minus (S left) (S right) = minus left right

power : Nat -> Nat -> Nat
power base O       = S O
power base (S exp) = mult base $ power base exp

--------------------------------------------------------------------------------
-- Type class instances
--------------------------------------------------------------------------------

instance Eq Nat where
  Z == Z         = True
  (S l) == (S r) = l == r
  _ == _         = False

instance Cast Nat Int where
  cast O     = 0
  cast (S k) = 1 + cast k

instance Ord Nat where
  compare O O         = EQ
  compare O (S k)     = LT
  compare (S k) O     = GT
  compare (S x) (S y) = compare x y

instance Num Nat where
  (+) = plus
  (-) = minus
  (*) = mult

  fromInteger = intToNat where
      %assert_total
      intToNat : Int -> Nat
      intToNat 0 = O
      intToNat n = if (n > 0) then S (fromInteger (n-1)) else O

--------------------------------------------------------------------------------
-- Division and modulus
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- Auxilliary notions
--------------------------------------------------------------------------------

pred : Nat -> Nat
pred O     = O
pred (S n) = n

--------------------------------------------------------------------------------
-- Fibonacci and factorial
--------------------------------------------------------------------------------

fib : Nat -> Nat
fib O         = O
fib (S O)     = S O
fib (S (S n)) = plus (fib (S n)) (fib n)

--------------------------------------------------------------------------------
-- GCD and LCM
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- Comparisons
--------------------------------------------------------------------------------

data LTE  : Nat -> Nat -> Set where
  lteZero : LTE O    right
  lteSucc : LTE left right -> LTE (S left) (S right)

GTE : Nat -> Nat -> Set
GTE left right = LTE right left

LT : Nat -> Nat -> Set
LT left right = LTE (S left) right

GT : Nat -> Nat -> Set
GT left right = LT right left

lte : Nat -> Nat -> Bool
lte O        right     = True
lte left     O         = False
lte (S left) (S right) = lte left right

gte : Nat -> Nat -> Bool
gte left right = lte right left

lt : Nat -> Nat -> Bool
lt left right = lte (S left) right

gt : Nat -> Nat -> Bool
gt left right = lt right left

minimum : Nat -> Nat -> Nat
minimum left right =
  if lte left right then
    left
  else
    right

maximum : Nat -> Nat -> Nat
maximum left right =
  if lte left right then
    right
  else
    left

--------------------------------------------------------------------------------
-- Properties
--------------------------------------------------------------------------------

-- Succ
succMonotonic : (left : Nat) -> (right : Nat) -> (p : left = right) ->
  S left = S right
succMonotonic left right refl = refl

succInjective : (left : Nat) -> (right : Nat) -> (p : S left = S right) ->
  left = right
succInjective left right refl = refl

-- Plus
plusZeroLeftNeutral : (right : Nat) -> plus O right = right
plusZeroLeftNeutral right = refl

plusZeroRightNeutral : (left : Nat) -> plus left O = left
plusZeroRightNeutral O     = refl
plusZeroRightNeutral (S n) =
  let inductiveHypothesis = plusZeroRightNeutral n in
    ?plusZeroRightNeutralStepCase

plusSuccRightSucc : (left : Nat) -> (right : Nat) ->
  S (plus left right) = plus left (S right)
plusSuccRightSucc O right        = refl
plusSuccRightSucc (S left) right =
  let inductiveHypothesis = plusSuccRightSucc left right in
    ?plusSuccRightSuccStepCase

plusCommutative : (left : Nat) -> (right : Nat) ->
  plus left right = plus right left
plusCommutative O        right = ?plusCommutativeBaseCase
plusCommutative (S left) right =
  let inductiveHypothesis = plusCommutative left right in
    ?plusCommutativeStepCase

plusAssociative : (left : Nat) -> (centre : Nat) -> (right : Nat) ->
  plus left (plus centre right) = plus (plus left centre) right
plusAssociative O        centre right = refl
plusAssociative (S left) centre right =
  let inductiveHypothesis = plusAssociative left centre right in
    ?plusAssociativeStepCase

plusMonotonicRight : (left : Nat) -> (right : Nat) -> (c : Nat) ->
  (p : left = right) -> plus left c = plus right c
plusMonotonicRight left right c refl = refl

plusMonotonicLeft : (left : Nat) -> (right : Nat) -> (c : Nat) ->
  (p : left = right) -> plus c left = plus c right
plusMonotonicLeft left right c refl = refl

plusOneSucc : (right : Nat) -> plus (S O) right = S right
plusOneSucc n = refl

-- Mult
multZeroLeftZero : (right : Nat) -> mult O right = O
multZeroLeftZero right = refl

multZeroRightZero : (left : Nat) -> mult left O = O
multZeroRightZero O        = refl
multZeroRightZero (S left) =
  let inductiveHypothesis = multZeroRightZero left in
    ?multZeroRightZeroStepCase

multRightSuccPlus : (left : Nat) -> (right : Nat) ->
  mult left (S right) = plus left (mult left right)
multRightSuccPlus O        right = refl
multRightSuccPlus (S left) right =
  let inductiveHypothesis = multRightSuccPlus left right in
    ?multRightSuccPlusStepCase

multLeftSuccPlus : (left : Nat) -> (right : Nat) ->
  mult (S left) right = plus right (mult left right)
multLeftSuccPlus left right = refl

multCommutative : (left : Nat) -> (right : Nat) ->
  mult left right = mult right left
multCommutative O right        = ?multCommutativeBaseCase
multCommutative (S left) right =
  let inductiveHypothesis = multCommutative left right in
    ?multCommutativeStepCase

multDistributesOverPlusRight : (left : Nat) -> (centre : Nat) -> (right : Nat) ->
  mult left (plus centre right) = plus (mult left centre) (mult left right)
multDistributesOverPlusRight O        centre right = refl
multDistributesOverPlusRight (S left) centre right =
  let inductiveHypothesis = multDistributesOverPlusRight left centre right in
    ?multDistributesOverPlusRightStepCase

multDistributesOverPlusLeft : (left : Nat) -> (centre : Nat) -> (right : Nat) ->
  mult (plus left centre) right = plus (mult left right) (mult centre right)
multDistributesOverPlusLeft O        centre right = refl
multDistributesOverPlusLeft (S left) centre right =
  let inductiveHypothesis = multDistributesOverPlusLeft left centre right in
    ?multDistributesOverPlusLeftStepCase

multAssociative : (left : Nat) -> (centre : Nat) -> (right : Nat) ->
  mult left (mult centre right) = mult (mult left centre) right
multAssociative O        centre right = refl
multAssociative (S left) centre right =
  let inductiveHypothesis = multAssociative left centre right in
    ?multAssociativeStepCase

multOneLeftNeutral : (right : Nat) -> mult (S O) right = right
multOneLeftNeutral O         = refl
multOneLeftNeutral (S right) =
  let inductiveHypothesis = multOneLeftNeutral right in
    ?multOneLeftNeutralStepCase

multOneRightNeutral : (left : Nat) -> mult left (S O) = left
multOneRightNeutral O        = refl
multOneRightNeutral (S left) =
  let inductiveHypothesis = multOneRightNeutral left in
    ?multOneRightNeutralStepCase

-- Minus
minusSuccSucc : (left : Nat) -> (right : Nat) ->
  minus (S left) (S right) = minus left right
minusSuccSucc left right = refl

minusZeroLeft : (right : Nat) -> minus O right = O
minusZeroLeft right = refl

minusZeroRight : (left : Nat) -> minus left O = left
minusZeroRight O        = refl
minusZeroRight (S left) = refl

minusZeroN : (n : Nat) -> O = minus n n
minusZeroN O     = refl
minusZeroN (S n) = minusZeroN n

minusOneSuccN : (n : Nat) -> S O = minus (S n) n
minusOneSuccN O     = refl
minusOneSuccN (S n) = minusOneSuccN n

-- Power
powerSuccPowerLeft : (base : Nat) -> (exp : Nat) -> power base (S exp) =
  mult base (power base exp)
powerSuccPowerLeft base exp = refl

multPowerPowerPlus : (base : Nat) -> (exp : Nat) -> (exp' : Nat) ->
  mult (power base exp) (power base exp') = power base (plus exp exp')
multPowerPowerPlus base O       exp' = ?multPowerPowerPlusBaseCase
multPowerPowerPlus base (S exp) exp' =
  let inductiveHypothesis = multPowerPowerPlus base exp exp' in
    ?multPowerPowerPlusStepCase

powerZeroOne : (base : Nat) -> power base O = S O
powerZeroOne base = refl

powerOneNeutral : (base : Nat) -> power base (S O) = base
powerOneNeutral O        = refl
powerOneNeutral (S base) =
  let inductiveHypothesis = powerOneNeutral base in
    ?powerOneNeutralStepCase

powerOneSuccOne : (exp : Nat) -> power (S O) exp = S O
powerOneSuccOne O       = refl
powerOneSuccOne (S exp) =
  let inductiveHypothesis = powerOneSuccOne exp in
    ?powerOneSuccOneStepCase

powerSuccSuccMult : (base : Nat) -> power base (S (S O)) = mult base base
powerSuccSuccMult O        = refl
powerSuccSuccMult (S base) =
  let inductiveHypothesis = powerSuccSuccMult base in
    ?powerSuccSuccMultStepCase

powerPowerMultPower : (base : Nat) -> (exp : Nat) -> (exp' : Nat) ->
  power (power base exp) exp' = power base (mult exp exp')
powerPowerMultPower base exp O        = ?powerPowerMultPowerBaseCase
powerPowerMultPower base exp (S exp') =
  let inductiveHypothesis = powerPowerMultPower base exp exp' in
    ?powerPowerMultPowerStepCase

-- Pred
predSucc : (n : Nat) -> pred (S n) = n
predSucc n = refl

minusSuccPred : (left : Nat) -> (right : Nat) ->
  minus left (S right) = pred (minus left right)
minusSuccPred O        right = refl
minusSuccPred (S left) O =
  let inductiveHypothesis = minusSuccPred left O in
    ?minusSuccPredStepCase
minusSuccPred (S left) (S right) =
  let inductiveHypothesis = minusSuccPred left right in
    ?minusSuccPredStepCase'

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
    rewrite sym (plusZeroRightNeutral (power (S O) exp));
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

