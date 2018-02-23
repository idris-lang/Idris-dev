module Data.PosNat

import Data.So

%default total
%access public export

||| ℤ⁺
PosNat : Type
PosNat = DPair Nat IsSucc

||| A proof that
plusPos : (n, k : Nat) -> IsSucc n -> IsSucc (n + k)
plusPos (S n) k pn = ItIsSucc

plusPosNat : PosNat -> PosNat -> PosNat
plusPosNat (n ** pn) (k ** _) = (n + k ** plusPos n k pn)

plusNatPosNat : Nat -> PosNat -> PosNat
plusNatPosNat n (S k ** pk) = (S $ k + n ** ItIsSucc)

timesPos : (n, k : Nat) -> IsSucc n -> IsSucc k -> IsSucc (n * k)
timesPos n@(S _) k@(S _) pn pk = ItIsSucc

multPosNat : PosNat -> PosNat -> PosNat
multPosNat (n ** pn) (k ** pk) = (n * k ** timesPos n k pn pk)

one : PosNat
one = (1 ** ItIsSucc)

succ : PosNat -> PosNat
succ (n ** _) = (S n ** ItIsSucc)

Semigroup PosNat where
  (<+>) = plusPosNat

p : (n : Nat) -> {auto ok : IsSucc n} -> PosNat
p Z {ok} impossible
p k {ok} = (k ** ok)
