import Data.Vect

foo : Nat -> Nat -> Nat
foo k j = ?foo_rhs1

append : (n : Nat) -> (m : Nat) -> Vect n a -> Vect m a -> Vect (n + m) a
append Z m [] ys = ys
append (S k) m (x :: xs) ys = x :: ?append_rhs1

