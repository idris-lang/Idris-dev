module NatCmp

data Cmp : Nat -> Nat -> Type where
     cmpLT : (y : _) -> Cmp x (x + S y)
     cmpEQ : Cmp x x
     cmpGT : (x : _) -> Cmp (y + S x) y

total cmp : (x, y : Nat) -> Cmp x y
cmp O O     = cmpEQ
cmp O (S k) = cmpLT _
cmp (S k) O = cmpGT _
cmp (S x) (S y) with (cmp x y)
  cmp (S x) (S (x + (S k))) | cmpLT k = cmpLT k
  cmp (S x) (S x)           | cmpEQ   = cmpEQ
  cmp (S (y + (S k))) (S y) | cmpGT k = cmpGT k
