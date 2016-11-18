module Prelude.Bool

import Builtins

import Prelude.Uninhabited

%access public export

||| Boolean Data Type
%case data Bool = False | True

||| The underlying implementation of the if ... then ... else ... syntax
||| @ b the condition on the if
||| @ t the value if b is true
||| @ e the falue if b is false
ifThenElse : (b : Bool) -> (t : Lazy a) -> (e : Lazy a) -> a
ifThenElse True  t e = t
ifThenElse False t e = e

-- Boolean Operator Precedence
infixl 4 &&, ||

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

||| A wrapper for Bool that specifies the semigroup and monoid implementations that use (&&)
data All : Type where
  GetAll : Bool -> All

Semigroup All where
  (GetAll left) <+> (GetAll right) = GetAll $ left && right

Monoid All where
  neutral = GetAll True

||| A wrapper for Bool that specifies the semigroup and monoid implementations that use (||)
data Any : Type where
  GetAny : Bool -> Any

Semigroup Any where
  (GetAny left) <+> (GetAny right) = GetAny $ left || right

Monoid Any where
  neutral = GetAny False

