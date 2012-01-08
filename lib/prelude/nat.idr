module prelude.nat

import builtins
import prelude.cast

%access public

data Nat = O | S Nat

instance Cast Nat Int where
    cast O = 0
    cast (S k) = 1 + cast k

plus : Nat -> Nat -> Nat
plus O     y = y
plus (S k) y = S (plus k y)

eqRespS : m = n -> S m = S n
eqRespS refl = refl

eqRespS' : S m = S n -> m = n
eqRespS' refl = refl

sub : Nat -> Nat -> Nat
sub O      y    = O
sub (S k) (S y) = sub k y
sub x      O    = x

mult : Nat -> Nat -> Nat
mult O     y = O
mult (S k) y = plus y (mult k y)

instance Eq Nat where 
    O     == O     = True
    (S x) == (S y) = x == y
    O     == (S y) = False
    (S x) == O     = False

instance Ord Nat where
    compare O O     = EQ
    compare O (S k) = LT
    compare (S k) O = GT
    compare (S x) (S y) = compare x y

instance Num Nat where
    (+) = plus
    (-) = sub
    (*) = mult

    fromInteger 0 = O
    fromInteger n = if (n > 0) then (S (fromInteger (n-1))) else O

plusnO : (m : Nat) -> m + O = m
plusnO O     = refl
plusnO (S k) = eqRespS (plusnO k)

plusn_Sm : (n, m : Nat) -> (plus n (S m)) = S (plus n m)
plusn_Sm O     m = refl
plusn_Sm (S j) m = eqRespS (plusn_Sm _ _)

plus_commutes : (n : Nat) -> (m : Nat) -> n + m = m + n
plus_commutes O     m = sym (plusnO m)
plus_commutes (S k) m = let ih = plus_commutes k m in ?plus_commutes_Sk

plus_commutes_Sk = proof {
    intro k,m,ih;
    refine sym;
    rewrite (sym ih);
    refine plusn_Sm;
}

plus_assoc : (n, m, p : Nat) -> n + (m + p) = (n + m) + p
plus_assoc O     m p = refl
plus_assoc (S k) m p = let ih = plus_assoc k m p in eqRespS ih

data Cmp : Nat -> Nat -> Set where
    cmpLT : (y : Nat) -> Cmp x (x + S y)
    cmpEQ : Cmp x x
    cmpGT : (x : Nat) -> Cmp (y + S x) y
  
cmp : (n, m : Nat) -> Cmp n m
cmp O     O     = cmpEQ
cmp (S n) O     = cmpGT _
cmp O     (S n) = cmpLT _
cmp (S x) (S y) with (cmp x y)
    cmp (S x) (S x)         | cmpEQ = cmpEQ
    cmp (S (y + S x)) (S y) | cmpGT _ = cmpGT _
    cmp (S x) (S (x + S y)) | cmpLT _ = cmpLT _
  
multnO : (n : Nat) -> (n * O) = O
multnO O     = refl
multnO (S k) = multnO k

multn_Sm : (n, m : Nat) -> n * S m = n + n * m
multn_Sm O     m = refl
multn_Sm (S k) m = let ih = multn_Sm k m in ?multnSmSk

mult_commutes : (n, m : Nat) -> n * m = m * n
mult_commutes O     m = ?mult_commO
mult_commutes (S k) m = let ih = mult_commutes k m in ?mult_commSk

mult_commSk = proof {
    intros;
    rewrite sym ih;
    rewrite multn_Sm m k;
    trivial;
}

mult_commO = proof {
    intro;
    rewrite multnO m;
    trivial;
}

multnSmSk = proof {
    intros;
    rewrite plus_commutes (mult k m) m;
    rewrite sym (plus_assoc k (mult k m) m);
    rewrite ih;
    rewrite plus_commutes m (mult k (S m));
    trivial;
}

