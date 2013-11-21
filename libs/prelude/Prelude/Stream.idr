module Prelude.Stream

import Prelude.Vect

codata Stream : Type -> Type where
  (::) : a -> Stream a -> Stream a

take : (n : Nat) -> Stream a -> Vect n a
take Z _ = []
take (S n) (x :: xs) = x :: (take n xs)
