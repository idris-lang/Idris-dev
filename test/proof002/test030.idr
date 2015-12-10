module test030

import Reflect

total
testReflect0 : (xs, ys : List a) -> ((xs ++ (ys ++ xs)) = ((xs ++ ys) ++ xs))
testReflect0 {a} xs ys = AssocProof a

total
testReflect1 : (xs, ys : List a) ->
               ((xs ++ (x :: ys ++ xs)) = ((xs ++ [x]) ++ (ys ++ xs)))
testReflect1 {a} xs ys = AssocProof a
