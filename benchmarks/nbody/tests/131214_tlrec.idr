module Main

import Data.Floats
import Data.Fin
import Data.Vect
import Data.Vect.Quantifiers
import Decidable.Equality

nums : Vect 5 Nat
nums = [4,5,6,7,8]

ix : Nat 
ix = length nums

my_sum : Fin (length nums) -> Nat -> Nat
my_sum i v = if i == fromNat 4 -- works
                 then v
                 else my_sum (succ i) (p + v) where p = index i nums


{-
finFour : Fin ix
finFour = fromNat 4

my_sum : Fin ix -> Nat -> Nat
my_sum finFour v = v
my_sum i v = my_sum (succ i) (p + v) where p = index i nums

my_sum n v with (n == 4)
| True = v
| False = my_sum (succ i) (p + v) where p = index i nums -}

main : Nat
main = my_sum 0 0

