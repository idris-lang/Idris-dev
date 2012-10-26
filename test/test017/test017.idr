module scg

%default total

data Ord = Zero | Suc Ord | Sup (Nat -> Ord)

natElim : (n : Nat) -> (P : Nat -> Set) ->
          (P O) -> ((n : Nat) -> (P n) -> (P (S n))) -> (P n)
natElim O     P mO mS = mO
natElim (S k) P mO mS = mS k (natElim k P mO mS)

ordElim : (x : Ord) ->
          (P : Ord -> Set) ->
          (P Zero) ->
          ((x : Ord) -> P x -> P (Suc x)) ->
          ((f : Nat -> Ord) -> ((n : Nat) -> P (f n)) -> 
             P (Sup f)) -> P x
ordElim Zero P mZ mSuc mSup = mZ
ordElim (Suc o) P mZ mSuc mSup = mSuc o (ordElim o P mZ mSuc mSup)
ordElim (Sup f) P mZ mSuc mSup =
   mSup f (\n => ordElim (f n) P mZ mSuc mSup)

myplus' : Nat -> Nat -> Nat
myplus : Nat -> Nat -> Nat

myplus O y     = y
myplus (S k) y = S (myplus' k y)

myplus' O y     = y
myplus' (S k) y = S (myplus y k)

mnubBy : (a -> a -> Bool) -> List a -> List a
mnubBy = nubBy' []
  where
    nubBy' : List a -> (a -> a -> Bool) -> List a -> List a
    nubBy' acc p []      = []
    nubBy' acc p (x::xs) =
      if elemBy p x acc then
        nubBy' acc p xs
      else
        x :: nubBy' (x::acc) p xs

partial
vtrans : Vect a n -> Vect a n -> List a
vtrans [] _         = []
vtrans (x :: xs) ys = x :: vtrans ys ys

even : Nat -> Bool
even O = True
even (S k) = odd k
  where
    odd : Nat -> Bool
    odd O = False
    odd (S k) = even k

ack : Nat -> Nat -> Nat
ack O     n     = S n
ack (S m) O     = ack m (S O)
ack (S m) (S n) = ack m (ack (S m) n) 

data Bin = eps | c0 Bin | c1 Bin

foo : Bin -> Nat
foo eps = O
foo (c0 eps) = O
foo (c0 (c1 x)) = S (foo (c1 x))
foo (c0 (c0 x)) = foo (c0 x)
foo (c1 x) = S (foo x)

bar : Nat -> Nat -> Nat
bar x y = mp x y where
  mp : Nat -> Nat -> Nat
  mp O y = y
  mp (S k) y = S (bar k y)

total mfib : Nat -> Nat
mfib O         = O
mfib (S O)     = S O
mfib (S (S n)) = mfib (S n) + mfib n

maxCommutative : (left : Nat) -> (right : Nat) ->
  maximum left right = maximum right left
maxCommutative O        O         = refl
maxCommutative (S left) O         = refl
maxCommutative O        (S right) = refl
maxCommutative (S left) (S right) =
    let inductiveHypothesis = maxCommutative left right in
        ?maxCommutativeStepCase

maxCommutativeStepCase = proof {
    intros;
    rewrite (boolElimSuccSucc (lte left right) right left);
    rewrite (boolElimSuccSucc (lte right left) left right);
    rewrite inductiveHypothesis;
    trivial;
}
