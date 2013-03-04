module Relation.Nat

import Relation.Binary

%access public
%default total

data LTEQ : Rel Nat where
  OrdBase : LTEQ O n
  OrdStep : LTEQ m n -> LTEQ (S m) (S n)

-- create other relations from LTEQ

GTEQ : Rel Nat
GTEQ m n = LTEQ n m

Relation.Nat.LT : Rel Nat
Relation.Nat.LT m n = LTEQ m (S n)

Relation.Nat.GT : Rel Nat
Relation.Nat.GT m n = Relation.Nat.LT n m

NotLTEQ : Rel Nat
NotLTEQ m n = (LTEQ m n) -> _|_

NotGTEQ : Rel Nat
NotGTEQ m n = (GTEQ m n) -> _|_

NotLT : Rel Nat
NotLT m n = (Relation.Nat.LT m n) -> _|_

NotGT : Rel Nat
NotGT m n = (Relation.Nat.GT m n) -> _|_

-- functions

isGreaterEqualOrLess : (m, n : Nat) -> Either (GTEQ m n) (Relation.Nat.LT m n)
isGreaterEqualOrLess O     O     = Left OrdBase
isGreaterEqualOrLess (S m) O     = Left OrdBase
isGreaterEqualOrLess O     (S n) = Right OrdBase
isGreaterEqualOrLess (S m) (S n) with (isGreaterEqualOrLess m n)
  | Left p = Left (OrdStep p)
  | Right p = Right (OrdStep p)
