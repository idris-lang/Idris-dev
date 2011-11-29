module nat;

import builtins;

data Nat = O | S Nat;

plus : Nat -> Nat -> Nat;
plus O     y = y;
plus (S k) y = S (plus k y);

eqRespS : m = n -> S m = S n;
eqRespS refl = refl;

eqRespS' : S m = S n -> m = n;
eqRespS' refl = refl;

sub : Nat -> Nat -> Nat;
sub O      y    = O;
sub (S k) (S y) = sub k y;
sub x      O    = x;

mult : Nat -> Nat -> Nat;
mult O     y = O;
mult (S k) y = plus y (mult k y);

instance Eq Nat where {
    O     == O     = True;
    (S x) == (S y) = x == y;
    O     == (S y) = False;
    (S x) == O     = False;
    
    x /= y = not (x == y);
}

instance Num Nat where {
    (+) = plus;
    (-) = sub;
    (*) = mult;

    fromInteger n = if (n > 0) then (S (fromInteger (n-1))) else O;
}

instance Ord Nat where {
    compare O O     = EQ;
    compare O (S k) = LT;
    compare (S k) O = GT;
    compare (S x) (S y) = compare x y;
}

plusnO : (m : Nat) -> m + O = m;
plusnO O     = refl;
plusnO (S k) = eqRespS (plusnO k);

plusn_Sm : (n : Nat) -> (m : Nat) -> n + S m = S (n + m);
plusn_Sm O     m = refl;
plusn_Sm (S j) m = eqRespS (plusn_Sm _ _);

plus_commutes : (n : Nat) -> (m : Nat) -> n + m = m + n;
plus_commutes O     m = sym (plusnO m);
plus_commutes (S k) m = let ih = plus_commutes k m in ?plus_commutes_Sk;

plus_commutes_Sk = proof {
    intro k,m,ih;
    refine sym;
    rewrite (sym ih);
    refine plusn_Sm;
};

