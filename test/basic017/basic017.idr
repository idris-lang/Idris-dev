%auto_implicits off

data Vect : Nat -> Type -> Type where
     Nil  : {a : _} -> Vect Z a
     (::) : {a, k : _} -> a -> Vect k a -> Vect (S k) a

data Elem  : {a, n : _} -> a -> Vect n a -> Type where
     Here  : {x, xs : _} -> Elem x (x :: xs)
     There : {x, y, xs : _} -> Elem x xs -> Elem x (y :: xs)

using (xs : Vect _ _)
  data Elem2  : {a, n : _} -> a -> Vect n a -> Type where
       Here2  : {x : _} -> Elem2 x (x :: xs)
       There2 : {x, y : _} -> Elem2 x xs -> Elem2 x (y :: xs)

append : {n, m, a : _} -> Vect n a -> Vect m a -> Vect (n + m) a
append [] ys = ys
append (x :: xs) ys = x :: append xs ys

%auto_implicits on

append2 : Vect n a -> Vect m a -> Vect (n + m) a
append2 [] ys = ys
append2 (x :: xs) ys = x :: append2 xs ys

