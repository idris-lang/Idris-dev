import Data.Vect

s1 : Num a => {x : a} -> x + sum {a} Nil = x -- * fromInteger 0
s1 = Refl

