module Canonicity
%default total

data ZeroSumList : Integer -> Type where
  Cons : (m : Integer) -> ZeroSumList n -> ZeroSumList (m + n)
  Nil : ZeroSumList 0

f : ZeroSumList 0 -> Nat
f Nil = 0

NaN : Nat
NaN = f (Cons 0 Nil)

