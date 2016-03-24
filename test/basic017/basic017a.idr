%auto_implicits off

data Vect : Nat -> Type -> Type where
     Nil  : {a : _} -> Vect Z a
     (::) : {a, k : _} -> a -> Vect k a -> Vect (S k) a

data Elem  : {a, n : _} -> a -> Vect n a -> Type where
     Here  : {x, xs : _} -> Elem x (x :: xs)
     There : {x, y, xs : _} -> Elem x xs -> Elem x (y :: xs)

append : Vect n a -> Vect m a -> Vect (n + m) a
append [] ys = ys
append (x :: xs) ys = x :: append xs ys


