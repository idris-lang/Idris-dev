module Prelude.Bool

import Builtins

import Prelude.Uninhabited

||| Boolean Data Type
%case data Bool = False | True

||| The underlying implementation of the if ... then ... else ... syntax
||| @ b the condition on the if
||| @ t the value if b is true
||| @ e the falue if b is false
boolElim : (b : Bool) -> (t : Lazy a) -> (e : Lazy a) -> a
boolElim True  t e = t
boolElim False t e = e

||| Ensure that some run-time Boolean test has been performed.
|||
||| This lifts a Boolean predicate to the type level. See the function `choose`
||| if you need to perform a Boolean test and convince the type checker of this
||| fact.
|||
||| If you find yourself using `so` for something other than primitive types,
||| it may be appropriate to define a type of evidence for the property that you
||| care about instead.
data so : Bool -> Type where oh : so True

instance Uninhabited (so False) where
  uninhabited oh impossible

-- Syntactic sugar for boolean elimination.
syntax if [test] then [t] else [e] = boolElim test (Delay t) (Delay e)

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

