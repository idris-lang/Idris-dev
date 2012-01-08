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

plusn_Sm : (n : Nat) -> (m : Nat) -> (plus n (S m)) = S (plus n m)
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

