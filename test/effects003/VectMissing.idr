module VectMissing

import Data.Fin
import Data.Vect

implementation Uninhabited (Elem x []) where
    uninhabited Here impossible

abstract
shrink : (xs : Vect (S n) a) -> Elem x xs -> Vect n a
shrink (x :: ys) Here = ys
shrink (y :: []) (There p) = absurd p
shrink (y :: (x :: xs)) (There p) = y :: shrink (x :: xs) p


