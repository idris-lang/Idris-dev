import nat;

data Fin : Nat -> Set where
    fO : Fin (S k)
  | fS : Fin k -> Fin (S k);

instance Eq (Fin n) where {
   fO == fO = True;
   (fS k) == (fS k') = k == k';
   _ == _ = False;

   x /= y = not (x == y);
}

infixr 7 :: ;

data Vect : Set -> Nat -> Set where
    VNil  : Vect a O
  | (::)  : a -> Vect a k -> Vect a (S k); 

vlookup : Fin n -> Vect a n -> a;
vlookup fO     (x :: xs) = x;
vlookup (fS k) (x :: xs) = vlookup k xs;
 
vapp : Vect a n -> Vect a m -> Vect a (n + m);
vapp VNil      ys = ys;
vapp (x :: xs) ys = x :: vapp xs ys;

vfilter : (a -> Bool) -> Vect a n -> (p ** Vect a p);
vfilter p VNil = ( _ ** VNil );
vfilter p (x :: xs) with (vfilter p xs) {
  vfilter p (x :: xs) | ( _ ** xs' ) 
     = if (p x) then ( _ ** x :: xs' ) else ( _ ** xs' );
}

