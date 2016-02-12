module Decidable.Order

import Decidable.Decidable
import Decidable.Equality
import Data.Fin
import Data.Fun
import Data.Rel

%access public export

--------------------------------------------------------------------------------
-- Utility Lemmas
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- Preorders, Posets, total Orders, Equivalencies, Congruencies
--------------------------------------------------------------------------------

interface Preorder t (po : t -> t -> Type) where
  total transitive : (a : t) -> (b : t) -> (c : t) -> po a b -> po b c -> po a c
  total reflexive : (a : t) -> po a a

interface (Preorder t po) => Poset t (po : t -> t -> Type) where
  total antisymmetric : (a : t) -> (b : t) -> po a b -> po b a -> a = b

interface (Poset t to) => Ordered t (to : t -> t -> Type) where
  total order : (a : t) -> (b : t) -> Either (to a b) (to b a)

interface (Preorder t eq) => Equivalence t (eq : t -> t -> Type) where
  total symmetric : (a : t) -> (b : t) -> eq a b -> eq b a

interface (Equivalence t eq) => Congruence t (f : t -> t) (eq : t -> t -> Type) where
  total congruent : (a : t) -> 
                    (b : t) -> 
                    eq a b -> 
                    eq (f a) (f b)

minimum : (Ordered t to) => t -> t -> t
minimum {to} x y with (order {to} x y)
  | Left _ = x
  | Right _ = y

maximum : (Ordered t to) => t -> t -> t
maximum {to} x y with (order {to} x y)
  | Left _ = y
  | Right _ = x

--------------------------------------------------------------------------------
-- Syntactic equivalence (=)
--------------------------------------------------------------------------------

implementation Preorder t ((=) {A = t} {B = t}) where
  transitive a b c = trans {a = a} {b = b} {c = c}
  reflexive a = Refl

implementation Equivalence t ((=) {A = t} {B = t}) where
  symmetric a b prf = sym prf

implementation Congruence t f ((=) {A = t} {B = t}) where
  congruent a b = cong {a = a} {b = b} {f = f}

--------------------------------------------------------------------------------
-- Natural numbers
--------------------------------------------------------------------------------

total LTEIsTransitive : (m : Nat) -> (n : Nat) -> (o : Nat) ->
                           LTE m n -> LTE n o ->
                           LTE m o
LTEIsTransitive Z n o                 LTEZero                  nlteo   = LTEZero
LTEIsTransitive (S m) (S n) (S o) (LTESucc mlten)    (LTESucc nlteo)   = LTESucc (LTEIsTransitive m n o mlten nlteo)

total LTEIsReflexive : (n : Nat) -> LTE n n
LTEIsReflexive Z      = LTEZero
LTEIsReflexive (S n)  = LTESucc (LTEIsReflexive n)

implementation Preorder Nat LTE where
  transitive = LTEIsTransitive
  reflexive  = LTEIsReflexive

total LTEIsAntisymmetric : (m : Nat) -> (n : Nat) ->
                              LTE m n -> LTE n m -> m = n
LTEIsAntisymmetric Z Z         LTEZero LTEZero = Refl
LTEIsAntisymmetric (S n) (S m) (LTESucc mLTEn) (LTESucc nLTEm) with (LTEIsAntisymmetric n m mLTEn nLTEm)
   LTEIsAntisymmetric (S n) (S n) (LTESucc mLTEn) (LTESucc nLTEm)    | Refl = Refl           


implementation Poset Nat LTE where
  antisymmetric = LTEIsAntisymmetric

total zeroNeverGreater : {n : Nat} -> LTE (S n) Z -> Void
zeroNeverGreater {n} LTEZero     impossible
zeroNeverGreater {n} (LTESucc _) impossible

total zeroAlwaysSmaller : {n : Nat} -> LTE Z n
zeroAlwaysSmaller = LTEZero

total ltesuccinjective : {n : Nat} -> {m : Nat} -> (LTE n m -> Void) -> LTE (S n) (S m) -> Void
ltesuccinjective {n} {m} disprf (LTESucc nLTEm) = void (disprf nLTEm)
ltesuccinjective {n} {m} disprf LTEZero         impossible


total decideLTE : (n : Nat) -> (m : Nat) -> Dec (LTE n m)
decideLTE    Z      y  = Yes LTEZero
decideLTE (S x)     Z  = No  zeroNeverGreater
decideLTE (S x)   (S y) with (decEq (S x) (S y))
  | Yes eq      = rewrite eq in Yes (reflexive (S y))
  | No _ with (decideLTE x y)
    | Yes nLTEm = Yes (LTESucc nLTEm)
    | No  nGTm  = No (ltesuccinjective nGTm)

implementation Decidable [Nat,Nat] LTE where
  decide = decideLTE

total
lte : (m : Nat) -> (n : Nat) -> Dec (LTE m n)
lte m n = decide {ts = [Nat,Nat]} {p = LTE} m n

total
shift : (m : Nat) -> (n : Nat) -> LTE m n -> LTE (S m) (S n)
shift m n mLTEn = LTESucc mLTEn
      
implementation Ordered Nat LTE where
  order Z      n = Left LTEZero
  order m      Z = Right LTEZero
  order (S k) (S j) with (order {to=LTE} k j)
    order (S k) (S j) | Left  prf = Left  (shift k j prf)
    order (S k) (S j) | Right prf = Right (shift j k prf)

----------------------------------------------------------------------------------
---- Finite numbers
----------------------------------------------------------------------------------

using (k : Nat)
  data FinLTE : Fin k -> Fin k -> Type where
    FromNatPrf : {m : Fin k} -> {n : Fin k} -> LTE (finToNat m) (finToNat n) -> FinLTE m n

  implementation Preorder (Fin k) FinLTE where
    transitive m n o (FromNatPrf p1) (FromNatPrf p2) = 
      FromNatPrf (LTEIsTransitive (finToNat m) (finToNat n) (finToNat o) p1 p2)
    reflexive n = FromNatPrf (LTEIsReflexive (finToNat n))

  implementation Poset (Fin k) FinLTE where
    antisymmetric m n (FromNatPrf p1) (FromNatPrf p2) =
      finToNatInjective m n (LTEIsAntisymmetric (finToNat m) (finToNat n) p1 p2)
  
  implementation Decidable [Fin k, Fin k] FinLTE where
    decide m n with (decideLTE (finToNat m) (finToNat n))
      | Yes prf    = Yes (FromNatPrf prf)
      | No  disprf = No (\ (FromNatPrf prf) => disprf prf)

  implementation Ordered (Fin k) FinLTE where
    order m n =
      either (Left . FromNatPrf) 
             (Right . FromNatPrf)
             (order (finToNat m) (finToNat n))

