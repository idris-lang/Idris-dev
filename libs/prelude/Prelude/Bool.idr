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
