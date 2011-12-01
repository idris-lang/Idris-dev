module prelude.vect;

import prelude.nat;

data Fin : Nat -> Set where
    fO : Fin (S k)
  | fS : Fin k -> Fin (S k);

instance Eq (Fin n) where {
   fO == fO = True;
   (fS k) == (fS k') = k == k';
   _ == _ = False;
}

infixr 7 :: ;

data Vect : Set -> Nat -> Set where
    Nil   : Vect a O
  | (::)  : a -> Vect a k -> Vect a (S k); 

lookup : Fin n -> Vect a n -> a;
lookup fO     (x :: xs) = x;
lookup (fS k) (x :: xs) = lookup k xs;
 
app : Vect a n -> Vect a m -> Vect a (n + m);
app []        ys = ys;
app (x :: xs) ys = x :: app xs ys;

filter : (a -> Bool) -> Vect a n -> (p ** Vect a p);
filter p [] = ( _ ** [] );
filter p (x :: xs) with (filter p xs) {
  filter p (x :: xs) | ( _ ** xs' ) 
     = if (p x) then ( _ ** x :: xs' ) else ( _ ** xs' );
}

map : (a -> b) -> Vect a n -> Vect b n;
map f [] = [];
map f (x :: xs) = f x :: map f xs;

