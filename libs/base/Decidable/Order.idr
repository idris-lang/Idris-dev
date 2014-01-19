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

total zeroNeverGreater : {n : Nat} -> NatLTE (S n) Z -> _|_
zeroNeverGreater {n} (nLTESm _) impossible
zeroNeverGreater {n}  nEqn      impossible

total
nGTSm : {n : Nat} -> {m : Nat} -> (NatLTE n m -> _|_) -> NatLTE n (S m) -> _|_
nGTSm         disprf (nLTESm nLTEm) = FalseElim (disprf nLTEm)
nGTSm {n} {m} disprf (nEqn) impossible

total
decideNatLTE : (n : Nat) -> (m : Nat) -> Dec (NatLTE n m)
decideNatLTE    Z      Z  = Yes nEqn
decideNatLTE (S x)     Z  = No  zeroNeverGreater
decideNatLTE    x   (S y) with (decEq x (S y))
  | Yes eq      = rewrite eq in Yes nEqn
  | No _ with (decideNatLTE x y)
    | Yes nLTEm = Yes (nLTESm nLTEm)
    | No  nGTm  = No (nGTSm nGTm)

instance Decidable [Nat,Nat] NatLTE where
  decide = decideNatLTE

lte : (m : Nat) -> (n : Nat) -> Dec (NatLTE m n)
lte m n = decide {ts = [Nat,Nat]} {p = NatLTE} m n
