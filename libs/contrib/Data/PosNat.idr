module Data.PosNat

import Data.So

%default total
%access public export

||| ℤ⁺: {1..}.
PosNat : Type
PosNat = DPair Nat IsSucc

||| A proof that the addition of a natural number to a natural number that is
||| already positive doesn't make a difference
plusPos : (n, k : Nat) -> IsSucc n -> IsSucc (n + k)
plusPos (S n) k pn = ItIsSucc

|||| Add two PosNats
plusPosNat : PosNat -> PosNat -> PosNat
plusPosNat (n ** pn) (k ** _) = (n + k ** plusPos n k pn)

||| Add a Nat to a positive Nat
plusNatPosNat : Nat -> PosNat -> PosNat
plusNatPosNat n (S k ** pk) = (S $ k + n ** ItIsSucc)

||| The proof that one positive Nat times another is still positive
timesPos : (n, k : Nat) -> IsSucc n -> IsSucc k -> IsSucc (n * k)
timesPos n@(S _) k@(S _) pn pk = ItIsSucc

||| Multiply two PosNats
multPosNat : PosNat -> PosNat -> PosNat
multPosNat (n ** pn) (k ** pk) = (n * k ** timesPos n k pn pk)

||| 1
one : PosNat
one = (1 ** ItIsSucc)

||| The successor of a PosNat
succ : PosNat -> PosNat
succ (n ** _) = (S n ** ItIsSucc)

||| Semigroup using addition (this seems to be the more generally useful case,
||| even though it doesn't form a Monoid)
Semigroup PosNat where
  (<+>) = plusPosNat

||| Semigroup using multiplication
[MultPosNatSemi] Semigroup PosNat where
  (<+>) = multPosNat

||| Monoid, neutral = 1
[MultPosNatMonoid] Monoid PosNat using MultPosNatSemi where
  neutral = one

||| Convert a Nat to a PosNat, using automatic proof search
p : (n : Nat) -> {auto ok : IsSucc n} -> PosNat
p Z {ok} impossible
p k {ok} = (k ** ok)
