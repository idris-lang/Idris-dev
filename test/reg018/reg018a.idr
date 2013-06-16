module conat

%default total

codata CoNat = Z | S CoNat

infinity : CoNat
infinity = S infinity

plusCoNat : CoNat -> CoNat -> CoNat
plusCoNat Z x = x
plusCoNat (S x) y = S (plusCoNat x y)

--I don't think this should be definable
minusCoNat : CoNat -> CoNat -> CoNat
minusCoNat Z n = Z
minusCoNat (S n) Z = S n
minusCoNat (S n) (S m) = plusCoNat Z (minusCoNat n m)

loopForever : CoNat
loopForever = minusCoNat infinity infinity
