import nat;

data Fin : Nat -> Set where
    fO : Fin (S k)
  | fS : Fin k -> Fin (S k);

infixr 7 :: ;

data Vect : Set -> Nat -> Set where
    VNil  : Vect a O
  | (::)  : a -> Vect a k -> Vect a (S k); 

vlookup : Fin n -> Vect a n -> a;
vlookup fO     (x :: xs) = x;
vlookup (fS k) (x :: xs) = vlookup k xs;
 
vapp : Vect a n -> Vect a m -> Vect a (plus n m);
vapp VNil      ys = ys;
vapp (x :: xs) ys = x :: vapp xs ys;

