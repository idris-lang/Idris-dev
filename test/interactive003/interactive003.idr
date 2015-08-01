import Data.Vect

app : Vect n a -> Vect m a -> Vect (n + m) a
app [] ys = ?app_rhs_1
app (x :: xs) ys = ?app_rhs_2
    
vzipWith : (a -> b -> c) -> Vect n a -> Vect n b -> Vect n c
vzipWith f [] [] = ?vzipWith_rhs_3
vzipWith f (x :: xs) (y :: ys) = ?vzipWith_rhs_1

word_length : Vect n String -> Vect n Nat
word_length [] = []
word_length (x :: xs) = ?word_length_rhs_2


