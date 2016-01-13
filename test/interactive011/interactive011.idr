import Data.Vect

data Foo = Bar | Baz

implementation Show Foo where

append : Vect n a -> Vect m a -> Vect (n + m) a
append (x :: xs) ys = ?append_rhs_2



