module scg

%default total

data Ord = Zero | Suc Ord | Sup (Nat -> Ord)

natElim : (n : Nat) -> (P : Nat -> Type) ->
          (P Z) -> ((n : Nat) -> (P n) -> (P (S n))) -> (P n)
natElim Z     P mO mS = mO
natElim (S k) P mO mS = mS k (natElim k P mO mS)

ordElim : (x : Ord) ->
          (P : Ord -> Type) ->
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

myplus Z y     = y
myplus (S k) y = S (myplus' k y)

myplus' Z y     = y
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
vtrans : Vect n a -> Vect n a -> List a
vtrans [] _         = []
vtrans (x :: xs) ys = x :: vtrans ys ys

even : Nat -> Bool
even Z = True
even (S k) = odd k
  where
    odd : Nat -> Bool
    odd Z = False
    odd (S k) = even k

ack : Nat -> Nat -> Nat
ack Z     n     = S n
ack (S m) Z     = ack m (S Z)
ack (S m) (S n) = ack m (ack (S m) n) 

data Bin = eps | c0 Bin | c1 Bin

foo : Bin -> Nat
foo eps = Z
foo (c0 eps) = Z
foo (c0 (c1 x)) = S (foo (c1 x))
foo (c0 (c0 x)) = foo (c0 x)
foo (c1 x) = S (foo x)

bar : Nat -> Nat -> Nat
bar x y = mp x y where
  mp : Nat -> Nat -> Nat
  mp Z y = y
  mp (S k) y = S (bar k y)

total mfib : Nat -> Nat
mfib Z         = Z
mfib (S Z)     = S Z
mfib (S (S n)) = mfib (S n) + mfib n

maxCommutative : (left : Nat) -> (right : Nat) ->
  maximum left right = maximum right left
maxCommutative Z        Z         = refl
maxCommutative (S left) Z         = refl
maxCommutative Z        (S right) = refl
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
