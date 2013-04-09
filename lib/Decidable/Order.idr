module Decidable.Order

import Decidable.Decidable
import Decidable.Equality

--------------------------------------------------------------------------------
-- Utility Lemmas
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- Preorders and Posets
--------------------------------------------------------------------------------

using (t : Type)
  data Preorder : (t -> t -> Type) -> Type where
    transRefl : ((a : t) -> (b : t) -> (c : t) -> po a b -> po b c -> po a c) ->
                ((a : t) -> po a a) ->
                Preorder po


  data Poset : (t -> t -> Type) -> Type where
    preorderAntisym : Preorder {t = t} po -> 
                      ((a : t) -> (b : t) -> po a b -> po b a -> a = b) -> 
                      Poset po

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

NatLTEIsPreorder : Preorder NatLTE
NatLTEIsPreorder = transRefl NatLTEIsTransitive NatLTEIsReflexive

total NatLTEIsAntisymmetric : (m : Nat) -> (n : Nat) -> po m n -> po n m -> m = n
NatLTEIsAntisymmetric n n nEqn nEqn = refl
NatLTEIsAntisymmetric n m nEqn (nLTESm _) impossible
NatLTEIsAntisymmetric n m (nLTESm _) nEqn impossible

NatLTEIsPoset : Poset NatLTE
NatLTEIsPoset = preorderAntisym NatLTEIsPreorder NatLTEIsAntisymmetric

total zeroNeverGreater : {n : Nat} -> NatLTE (S n) O -> _|_
zeroNeverGreater {n} (nLTESm _) impossible
zeroNeverGreater {n}  nEqn      impossible

total
nGTSm : {n : Nat} -> {m : Nat} -> (NatLTE n m -> _|_) -> NatLTE n (S m) -> _|_
nGTSm         disprf (nLTESm nLTEm) = FalseElim (disprf nLTEm)
nGTSm {n} {m} disprf (nEqn) impossible

total
decideNatLTE : (n : Nat) -> (m : Nat) -> Dec (NatLTE n m)
decideNatLTE    O      O  = Yes nEqn
decideNatLTE (S x)     O  = No  zeroNeverGreater
decideNatLTE    x   (S y) with (decEq x (S y))
  | Yes eq      = rewrite eq in Yes nEqn
  | No _ with (decideNatLTE x y)
    | Yes nLTEm = Yes (nLTESm nLTEm)
    | No  nGTm  = No (nGTSm nGTm)

instance Rel NatLTE where
  liftRel f = (n : Nat) -> (m : Nat) -> f (NatLTE n m)

instance Decidable NatLTE where
  decide = decideNatLTE

