module Decidable.Order

import Decidable.Decidable
import Decidable.Equality

%access public

--------------------------------------------------------------------------------
-- Utility Lemmas
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- Preorders and Posets
--------------------------------------------------------------------------------

class Preorder t (po : t -> t -> Type) where
  total transitive : (a : t) -> (b : t) -> (c : t) -> po a b -> po b c -> po a c
  total reflexive : (a : t) -> po a a

class (Preorder t po) => Poset t (po : t -> t -> Type) where
  total antisymmetric : (a : t) -> (b : t) -> po a b -> po b a -> a = b

--------------------------------------------------------------------------------
-- Natural numbers
--------------------------------------------------------------------------------

data NatLTE : Nat -> Nat -> Type where
  nEqn   : NatLTE n n
  nLTESm : NatLTE n m -> NatLTE n (S m)

total NatLTEIsTransitive : (m : Nat) -> (n : Nat) -> (o : Nat) ->
                           NatLTE m n -> NatLTE n o ->
                           NatLTE m o
NatLTEIsTransitive m n n      mLTEn (nEqn) = mLTEn
NatLTEIsTransitive m n (S o)  mLTEn (nLTESm nLTEo)
  = nLTESm (NatLTEIsTransitive m n o mLTEn nLTEo)

total NatLTEIsReflexive : (n : Nat) -> NatLTE n n
NatLTEIsReflexive _ = nEqn

instance Preorder Nat NatLTE where
  transitive = NatLTEIsTransitive
  reflexive  = NatLTEIsReflexive

total NatLTEIsAntisymmetric : (m : Nat) -> (n : Nat) -> 
                              NatLTE m n -> NatLTE n m -> m = n
NatLTEIsAntisymmetric n n nEqn nEqn = refl
NatLTEIsAntisymmetric n m nEqn (nLTESm _) impossible
NatLTEIsAntisymmetric n m (nLTESm _) nEqn impossible
NatLTEIsAntisymmetric n m (nLTESm _) (nLTESm _) impossible

instance Poset Nat NatLTE where
  antisymmetric = NatLTEIsAntisymmetric

total zeroNeverGreater : {n : Nat} -> NatLTE (S n) O -> _|_
zeroNeverGreater {n} (nLTESm _) impossible
zeroNeverGreater {n}  nEqn      impossible

total zeroAlwaysSmaler : (n : Nat) -> NatLTE O n
zeroAlwaysSmaler    O  = nEqn
zeroAlwaysSmaler (S n) = nLTESm (zeroAlwaysSmaler n)

total
nGTSm : {n : Nat} -> {m : Nat} -> (NatLTE n m -> _|_) -> NatLTE n (S m) -> _|_
nGTSm         disprf (nLTESm nLTEm) = FalseElim (disprf nLTEm)
nGTSm {n} {m} disprf (nEqn) impossible

total
shiftNatLTE : {n : Nat} -> {m : Nat} -> NatLTE n m -> NatLTE (S n) (S m)
shiftNatLTE nEqn = nEqn
shiftNatLTE (nLTESm nLTEpm) = nLTESm (shiftNatLTE nLTEpm)

total
natLTE : (n : Nat) -> (m : Nat) -> Dec (NatLTE n m)
natLTE    O      O  = Yes nEqn
natLTE (S x)     O  = No  zeroNeverGreater
natLTE    O   (S y) = Yes (zeroAlwaysSmaler (S y))
natLTE (S x)  (S y) with (natLTE x y)
  | Yes prf   = Yes (shiftNatLTE prf)
  | No disprf = No  (\ sxLTESy => nGTSm disprf (NatLTEIsTransitive x (S x) (S y) (nLTESm nEqn) sxLTESy))

total 
natLTECompleteness : {n : Nat} -> {m : Nat} -> NatLTE n m -> Given (natLTE n m)
natLTECompleteness {n} {m} nlte with (natLTE n m)
  | Yes prf    = always
  | No  disprf = FalseElim $ disprf nlte

total
natLTESoundness : {n : Nat} -> {m : Nat} -> (NatLTE n m -> _|_) -> Given (natLTE n m) -> _|_
natLTESoundness disprf always impossible

onNatLTE : PredicateFunctor
onNatLTE p = (n : Nat) -> (m : Nat) -> p (NatLTE n m)

instance Decidable onNatLTE where
  decide = natLTE

--lte : (m : Nat) -> (n : Nat) -> Dec (NatLTE m n)
--lte m n = decide {p = NatLTE} m n

