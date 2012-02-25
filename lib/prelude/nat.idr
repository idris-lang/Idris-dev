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

total isZero : Nat -> Bool
isZero O     = True
isZero (S n) = False

total isSucc : Nat -> Bool
isSucc O     = False
isSucc (S n) = True

--------------------------------------------------------------------------------
-- Basic arithmetic functions
--------------------------------------------------------------------------------

total plus : Nat -> Nat -> Nat
plus O right        = right
plus (S left) right = S (plus left right)

total mult : Nat -> Nat -> Nat
mult O right        = O
mult (S left) right = plus right $ mult left right

total minus : Nat -> Nat -> Nat
minus O        right     = O
minus left     O         = left
minus (S left) (S right) = minus left right

total power : Nat -> Nat -> Nat
power base O       = S O
power base (S exp) = mult base $ power base exp

--------------------------------------------------------------------------------
-- Comparisons
--------------------------------------------------------------------------------

data LTE  : Nat -> Nat -> Set where
  lteZero : LTE O    right
  lteSucc : LTE left right -> LTE (S left) (S right)

total GTE : Nat -> Nat -> Set
GTE left right = LTE right left

total LT : Nat -> Nat -> Set
LT left right = LTE (S left) right

total GT : Nat -> Nat -> Set
GT left right = LT right left

total lte : Nat -> Nat -> Bool
lte O        right     = True
lte left     O         = False
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
  O == O         = True
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

  abs x = x

  fromInteger = fromInteger'
    where
      %assert_total
      fromInteger' : Int -> Nat
      fromInteger' 0 = O
      fromInteger' n =
        if (n > 0) then
          S (fromInteger' (n - 1))
        else
          O

record Multiplicative : Set where
  getMultiplicative : Nat -> Multiplicative

record Additive : Set where
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
  neutral = getMultiplicative $ S O

instance Monoid Additive where
  neutral = getAdditive O

instance MeetSemilattice Nat where
  meet = minimum

instance JoinSemilattice Nat where
  join = maximum

instance Lattice Nat where { }

instance BoundedJoinSemilattice Nat where
  bottom = O

--------------------------------------------------------------------------------
-- Auxilliary notions
--------------------------------------------------------------------------------

total pred : Nat -> Nat
pred O     = O
pred (S n) = n

--------------------------------------------------------------------------------
-- Fibonacci and factorial
--------------------------------------------------------------------------------

total fib : Nat -> Nat
fib O         = O
fib (S O)     = S O
fib (S (S n)) = fib (S n) + fib n

--------------------------------------------------------------------------------
-- GCD and LCM
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- Division and modulus
--------------------------------------------------------------------------------

total mod : Nat -> Nat -> Nat
mod left O         = left
mod left (S right) = mod' left left right
  where
    total mod' : Nat -> Nat -> Nat -> Nat
    mod' O        centre right = centre
    mod' (S left) centre right =
      if lte centre right then
        centre
      else
        mod' left (centre - (S right)) right

total div : Nat -> Nat -> Nat
div left O         = S left               -- div by zero
div left (S right) = div' left left right
  where
    total div' : Nat -> Nat -> Nat -> Nat
    div' O        centre right = O
    div' (S left) centre right =
      if lte centre right then
        O
      else
        S (div' left (centre - (S right)) right)

--------------------------------------------------------------------------------
-- Properties
--------------------------------------------------------------------------------

-- Succ
total eqSucc : (left : Nat) -> (right : Nat) -> (p : left = right) ->
  S left = S right
eqSucc left right refl = refl

total succInjective : (left : Nat) -> (right : Nat) -> (p : S left = S right) ->
  left = right
succInjective left right refl = refl

-- Plus
total plusZeroLeftNeutral : (right : Nat) -> 0 + right = right
plusZeroLeftNeutral right = refl

total plusZeroRightNeutral : (left : Nat) -> left + 0 = left
plusZeroRightNeutral O     = refl
plusZeroRightNeutral (S n) =
  let inductiveHypothesis = plusZeroRightNeutral n in
    ?plusZeroRightNeutralStepCase

total plusSuccRightSucc : (left : Nat) -> (right : Nat) ->
  S (left + right) = left + (S right)
plusSuccRightSucc O right        = refl
plusSuccRightSucc (S left) right =
  let inductiveHypothesis = plusSuccRightSucc left right in
    ?plusSuccRightSuccStepCase

total plusCommutative : (left : Nat) -> (right : Nat) ->
  left + right = right + left
plusCommutative O        right = ?plusCommutativeBaseCase
plusCommutative (S left) right =
  let inductiveHypothesis = plusCommutative left right in
    ?plusCommutativeStepCase

total plusAssociative : (left : Nat) -> (centre : Nat) -> (right : Nat) ->
  left + (centre + right) = (left + centre) + right
plusAssociative O        centre right = refl
plusAssociative (S left) centre right =
  let inductiveHypothesis = plusAssociative left centre right in
    ?plusAssociativeStepCase

total plusConstantRight : (left : Nat) -> (right : Nat) -> (c : Nat) ->
  (p : left = right) -> left + c = right + c
plusConstantRight left right c refl = refl

total plusConstantLeft : (left : Nat) -> (right : Nat) -> (c : Nat) ->
  (p : left = right) -> c + left = c + right
plusConstantLeft left right c refl = refl

total plusOneSucc : (right : Nat) -> 1 + right = S right
plusOneSucc n = refl

total plusLeftCancel : (left : Nat) -> (right : Nat) -> (right' : Nat) ->
  (p : left + right = left + right') -> right = right'
plusLeftCancel O        right right' p = ?plusLeftCancelBaseCase
plusLeftCancel (S left) right right' p =
  let inductiveHypothesis = plusLeftCancel left right right' in
    ?plusLeftCancelStepCase

total plusRightCancel : (left : Nat) -> (left' : Nat) -> (right : Nat) ->
  (p : left + right = left' + right) -> left = left'
plusRightCancel left left' O         p = ?plusRightCancelBaseCase
plusRightCancel left left' (S right) p =
  let inductiveHypothesis = plusRightCancel left left' right in
    ?plusRightCancelStepCase

total plusLeftLeftRightZero : (left : Nat) -> (right : Nat) ->
  (p : left + right = left) -> right = O
plusLeftLeftRightZero O        right p = ?plusLeftLeftRightZeroBaseCase
plusLeftLeftRightZero (S left) right p =
  let inductiveHypothesis = plusLeftLeftRightZero left right in
    ?plusLeftLeftRightZeroStepCase

-- Mult
total multZeroLeftZero : (right : Nat) -> O * right = O
multZeroLeftZero right = refl

total multZeroRightZero : (left : Nat) -> left * O = O
multZeroRightZero O        = refl
multZeroRightZero (S left) =
  let inductiveHypothesis = multZeroRightZero left in
    ?multZeroRightZeroStepCase

total multRightSuccPlus : (left : Nat) -> (right : Nat) ->
  left * (S right) = left + (left * right)
multRightSuccPlus O        right = refl
multRightSuccPlus (S left) right =
  let inductiveHypothesis = multRightSuccPlus left right in
    ?multRightSuccPlusStepCase

total multLeftSuccPlus : (left : Nat) -> (right : Nat) ->
  (S left) * right = right + (left * right)
multLeftSuccPlus left right = refl

total multCommutative : (left : Nat) -> (right : Nat) ->
  left * right = right * left
multCommutative O right        = ?multCommutativeBaseCase
multCommutative (S left) right =
  let inductiveHypothesis = multCommutative left right in
    ?multCommutativeStepCase

total multDistributesOverPlusRight : (left : Nat) -> (centre : Nat) -> (right : Nat) ->
  left * (centre + right) = (left * centre) + (left * right)
multDistributesOverPlusRight O        centre right = refl
multDistributesOverPlusRight (S left) centre right =
  let inductiveHypothesis = multDistributesOverPlusRight left centre right in
    ?multDistributesOverPlusRightStepCase

total multDistributesOverPlusLeft : (left : Nat) -> (centre : Nat) -> (right : Nat) ->
  (left + centre) * right = (left * right) + (centre * right)
multDistributesOverPlusLeft O        centre right = refl
multDistributesOverPlusLeft (S left) centre right =
  let inductiveHypothesis = multDistributesOverPlusLeft left centre right in
    ?multDistributesOverPlusLeftStepCase

total multAssociative : (left : Nat) -> (centre : Nat) -> (right : Nat) ->
  left * (centre * right) = (left * centre) * right
multAssociative O        centre right = refl
multAssociative (S left) centre right =
  let inductiveHypothesis = multAssociative left centre right in
    ?multAssociativeStepCase

total multOneLeftNeutral : (right : Nat) -> 1 * right = right
multOneLeftNeutral O         = refl
multOneLeftNeutral (S right) =
  let inductiveHypothesis = multOneLeftNeutral right in
    ?multOneLeftNeutralStepCase

total multOneRightNeutral : (left : Nat) -> left * 1 = left
multOneRightNeutral O        = refl
multOneRightNeutral (S left) =
  let inductiveHypothesis = multOneRightNeutral left in
    ?multOneRightNeutralStepCase

-- Minus
total minusSuccSucc : (left : Nat) -> (right : Nat) ->
  (S left) - (S right) = left - right
minusSuccSucc left right = refl

total minusZeroLeft : (right : Nat) -> 0 - right = O
minusZeroLeft right = refl

total minusZeroRight : (left : Nat) -> left - 0 = left
minusZeroRight O        = refl
minusZeroRight (S left) = refl

total minusZeroN : (n : Nat) -> O = n - n
minusZeroN O     = refl
minusZeroN (S n) = minusZeroN n

total minusOneSuccN : (n : Nat) -> S O = (S n) - n
minusOneSuccN O     = refl
minusOneSuccN (S n) = minusOneSuccN n

total minusSuccOne : (n : Nat) -> S n - 1 = n
minusSuccOne O     = refl
minusSuccOne (S n) = refl

total minusPlusZero : (n : Nat) -> (m : Nat) -> n - (n + m) = O
minusPlusZero O     m = refl
minusPlusZero (S n) m = minusPlusZero n m

total minusMinusMinusPlus : (left : Nat) -> (centre : Nat) -> (right : Nat) ->
  left - centre - right = left - (centre + right)
minusMinusMinusPlus O        O          right = refl
minusMinusMinusPlus (S left) O          right = refl
minusMinusMinusPlus O        (S centre) right = refl
minusMinusMinusPlus (S left) (S centre) right =
  let inductiveHypothesis = minusMinusMinusPlus left centre right in
    ?minusMinusMinusPlusStepCase

total plusMinusLeftCancel : (left : Nat) -> (right : Nat) -> (right' : Nat) ->
  (left + right) - (left + right') = right - right'
plusMinusLeftCancel O right right'        = refl
plusMinusLeftCancel (S left) right right' =
  let inductiveHypothesis = plusMinusLeftCancel left right right' in
    ?plusMinusLeftCancelStepCase

total multDistributesOverMinusLeft : (left : Nat) -> (centre : Nat) -> (right : Nat) ->
  (left - centre) * right = (left * right) - (centre * right)
multDistributesOverMinusLeft O        O          right = refl
multDistributesOverMinusLeft (S left) O          right =
  ?multDistributesOverMinusLeftBaseCase
multDistributesOverMinusLeft O        (S centre) right = refl
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
multPowerPowerPlus base O       exp' = ?multPowerPowerPlusBaseCase
multPowerPowerPlus base (S exp) exp' =
  let inductiveHypothesis = multPowerPowerPlus base exp exp' in
    ?multPowerPowerPlusStepCase

total powerZeroOne : (base : Nat) -> power base 0 = S O
powerZeroOne base = refl

total powerOneNeutral : (base : Nat) -> power base 1 = base
powerOneNeutral O        = refl
powerOneNeutral (S base) =
  let inductiveHypothesis = powerOneNeutral base in
    ?powerOneNeutralStepCase

total powerOneSuccOne : (exp : Nat) -> power 1 exp = S O
powerOneSuccOne O       = refl
powerOneSuccOne (S exp) =
  let inductiveHypothesis = powerOneSuccOne exp in
    ?powerOneSuccOneStepCase

total powerSuccSuccMult : (base : Nat) -> power base 2 = mult base base
powerSuccSuccMult O        = refl
powerSuccSuccMult (S base) =
  let inductiveHypothesis = powerSuccSuccMult base in
    ?powerSuccSuccMultStepCase

total powerPowerMultPower : (base : Nat) -> (exp : Nat) -> (exp' : Nat) ->
  power (power base exp) exp' = power base (exp * exp')
powerPowerMultPower base exp O        = ?powerPowerMultPowerBaseCase
powerPowerMultPower base exp (S exp') =
  let inductiveHypothesis = powerPowerMultPower base exp exp' in
    ?powerPowerMultPowerStepCase

-- Pred
total predSucc : (n : Nat) -> pred (S n) = n
predSucc n = refl

total minusSuccPred : (left : Nat) -> (right : Nat) ->
  left - (S right) = pred (left - right)
minusSuccPred O        right = refl
minusSuccPred (S left) O =
  let inductiveHypothesis = minusSuccPred left O in
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
lteNTrue O     = refl
lteNTrue (S n) = lteNTrue n

total lteSuccZeroFalse : (n : Nat) -> lte (S n) O = False
lteSuccZeroFalse O     = refl
lteSuccZeroFalse (S n) = refl

-- Minimum and maximum
total minimumZeroZeroRight : (right : Nat) -> minimum 0 right = O
minimumZeroZeroRight O         = refl
minimumZeroZeroRight (S right) = minimumZeroZeroRight right

total minimumZeroZeroLeft : (left : Nat) -> minimum left 0 = O
minimumZeroZeroLeft O        = refl
minimumZeroZeroLeft (S left) = refl

total minimumSuccSucc : (left : Nat) -> (right : Nat) ->
  minimum (S left) (S right) = S (minimum left right)
minimumSuccSucc O        O         = refl
minimumSuccSucc (S left) O         = refl
minimumSuccSucc O        (S right) = refl
minimumSuccSucc (S left) (S right) =
  let inductiveHypothesis = minimumSuccSucc left right in
    ?minimumSuccSuccStepCase

total minimumCommutative : (left : Nat) -> (right : Nat) ->
  minimum left right = minimum right left
minimumCommutative O        O         = refl
minimumCommutative O        (S right) = refl
minimumCommutative (S left) O         = refl
minimumCommutative (S left) (S right) =
  let inductiveHypothesis = minimumCommutative left right in
    ?minimumCommutativeStepCase

total maximumZeroNRight : (right : Nat) -> maximum O right = right
maximumZeroNRight O         = refl
maximumZeroNRight (S right) = refl

total maximumZeroNLeft : (left : Nat) -> maximum left O = left
maximumZeroNLeft O        = refl
maximumZeroNLeft (S left) = refl

total maximumSuccSucc : (left : Nat) -> (right : Nat) ->
  S (maximum left right) = maximum (S left) (S right)
maximumSuccSucc O        O         = refl
maximumSuccSucc (S left) O         = refl
maximumSuccSucc O        (S right) = refl
maximumSuccSucc (S left) (S right) =
  let inductiveHypothesis = maximumSuccSucc left right in
    ?maximumSuccSuccStepCase

total maximumCommutative : (left : Nat) -> (right : Nat) ->
  maximum left right = maximum right left
maximumCommutative O        O         = refl
maximumCommutative (S left) O         = refl
maximumCommutative O        (S right) = refl
maximumCommutative (S left) (S right) =
  let inductiveHypothesis = maximumCommutative left right in
    ?maximumCommutativeStepCase

-- div and mod
total modZeroZero : (n : Nat) -> mod 0 n = O
modZeroZero O     = refl
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
    refine succInjective;
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

