module Prelude.Bool

import Builtins

import Prelude.Uninhabited

%access public export

||| Boolean Data Type
data Bool = False | True

||| The underlying implementation of the if ... then ... else ... syntax
||| @ b the condition on the if
||| @ t the value if b is true
||| @ e the value if b is false
ifThenElse : (b : Bool) -> (t : Lazy a) -> (e : Lazy a) -> a
ifThenElse True  t e = t
ifThenElse False t e = e

-- Boolean Operator Precedence
infixr 4 ||
infixr 5 &&

||| Boolean OR only evaluates the second argument if the first is `False`.
(||) : Bool -> Lazy Bool -> Bool
(||) False x = x
(||) True _  = True

||| Boolean AND only evaluates the second argument if the first is `True`.
(&&) : Bool -> Lazy Bool -> Bool
(&&) True x  = x
(&&) False _ = False

||| Boolean NOT
not : Bool -> Bool
not True = False
not False = True

--------------------------------------------------------------------------------
-- Properties
--------------------------------------------------------------------------------

Uninhabited (True = False) where
  uninhabited Refl impossible

Uninhabited (False = True) where
  uninhabited Refl impossible

-- Not

total doubleNotDisappears : (b : Bool) -> not (not b) = b
doubleNotDisappears True  = Refl
doubleNotDisappears False = Refl

-- Conjunction

total conjTrueRightNeutral : (b : Bool) -> b && True = b
conjTrueRightNeutral False = Refl
conjTrueRightNeutral True  = Refl

total conjTrueLeftNeutral : (b : Bool) -> True && b = b
conjTrueLeftNeutral _ = Refl

total conjFalseRightAbsorbs : (b : Bool) -> b && False = False
conjFalseRightAbsorbs False = Refl
conjFalseRightAbsorbs True  = Refl

total conjFalseLeftAbsorbs : (b : Bool) -> False && b = False
conjFalseLeftAbsorbs _ = Refl

total conjCommutative : (b : Bool) -> (c : Bool) -> b && c = c && b
conjCommutative False False = Refl
conjCommutative False True  = Refl
conjCommutative True  False = Refl
conjCommutative True  True  = Refl

total conjNotFalse : (b : Bool) -> b && not b = False
conjNotFalse False = Refl
conjNotFalse True  = Refl

-- Disjunction

total disjFalseRightNeutral : (b : Bool) -> b || False = b
disjFalseRightNeutral False = Refl
disjFalseRightNeutral True  = Refl

total disjFalseLeftNeutral : (b : Bool) -> False || b = b
disjFalseLeftNeutral _ = Refl

total disjTrueRightAbsorbs : (b : Bool) -> b || True = True
disjTrueRightAbsorbs False = Refl
disjTrueRightAbsorbs True  = Refl

total disjTrueLeftAbsorbs : (b : Bool) -> True || b = True
disjTrueLeftAbsorbs _ = Refl

total disjCommutative : (b : Bool) -> (c : Bool) -> b || c = c || b
disjCommutative False False = Refl
disjCommutative False True  = Refl
disjCommutative True  False = Refl
disjCommutative True  True  = Refl

total disjNotTrue : (b : Bool) -> b || not b = True
disjNotTrue False = Refl
disjNotTrue True  = Refl

-- De Morgan's Laws

total conjDeMorgan : (b : Bool) -> (c : Bool) -> not (b && c) = not b || not c
conjDeMorgan False _ = Refl
conjDeMorgan True  _ = Refl

total disjDeMorgan : (b : Bool) -> (c : Bool) -> not (b || c) = not b && not c
disjDeMorgan False _ = Refl
disjDeMorgan True  _ = Refl
