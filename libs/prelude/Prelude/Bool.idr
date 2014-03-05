module Prelude.Bool

||| Boolean Data Type
data Bool = False | True

||| The underlying implementation of the if ... then ... else ... syntax
||| @ b the condition on the if
||| @ t the value if b is true
||| @ e the falue if b is false
boolElim : (b : Bool) -> (t : Lazy a) -> (e : Lazy a) -> a
boolElim True  t e = t
boolElim False t e = e

||| Defines a predicate on Bool which guarantees that the value is true.
data so : Bool -> Type where oh : so True

-- Syntaxtic sugar for boolean elimination.
syntax if [test] then [t] else [e] = boolElim test (Delay t) (Delay e)

-- Boolean Operator Precedence
infixl 4 &&, ||

||| Boolean OR
(||) : Bool -> Bool -> Bool
(||) False x = x
(||) True _  = True

||| Boolean AND
(&&) : Bool -> Bool -> Bool
(&&) True x  = x
(&&) False _ = False

||| Boolean NOT
not : Bool -> Bool
not True = False
not False = True

