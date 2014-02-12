module Prelude.Bool

-- | Boolean Data Type
data Bool = False | True

-- | Boolean elimination
boolElim : Bool -> |(t : a) -> |(f : a) -> a
boolElim True  t e = force t
boolElim False t e = force e

-- | Defines a predicate on Bool which guarantees that the value is true.
data so : Bool -> Type where oh : so True

-- Syntaxtic sugar for boolean elimination.
syntax if [test] then [t] else [e] = boolElim test t e

-- Boolean Operator Precedence
infixl 4 &&, ||

-- | Boolean OR
(||) : Bool -> Bool -> Bool
(||) False x = x
(||) True _  = True

-- | Boolean AND
(&&) : Bool -> Bool -> Bool
(&&) True x  = x
(&&) False _ = False

-- | Boolean NOT
not : Bool -> Bool
not True = False
not False = True

