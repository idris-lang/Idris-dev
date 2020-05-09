module Decidable.Order

import Decidable.Decidable
import Decidable.Equality
import Data.Fin
import Data.Fun
import Data.Rel

%access public export
%default total

--------------------------------------------------------------------------------
-- Preorders, Posets, total Orders, Equivalencies, Congruencies
--------------------------------------------------------------------------------

interface Preorder t (po : t -> t -> Type) where
  transitive : (a, b, c : t) -> po a b -> po b c -> po a c
  reflexive : (a : t) -> po a a

interface (Preorder t po) => Poset t (po : t -> t -> Type) where
  antisymmetric : (a, b : t) -> po a b -> po b a -> a = b

interface (Poset t to) => Ordered t (to : t -> t -> Type) where
  order : (a, b : t) -> Either (to a b) (to b a)

interface (Preorder t eq) => Equivalence t (eq : t -> t -> Type) where
  symmetric : (a, b : t) -> eq a b -> eq b a

interface (Equivalence t eq) => Congruence t (f : t -> t) (eq : t -> t -> Type) where
  congruent : (a, b : t) -> eq a b -> eq (f a) (f b)

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

Preorder t (=) where
  transitive _ _ _ = trans
  reflexive _ = Refl

Equivalence t (=) where
  symmetric _ _ = sym

Congruence t f (=) where
  congruent _ _ = cong

--------------------------------------------------------------------------------
-- Natural numbers
--------------------------------------------------------------------------------

Preorder Nat LTE where
  transitive Z _ _ _ _ = LTEZero
  transitive (S m) (S n) (S o) (LTESucc mlten) (LTESucc nlteo) =
    LTESucc (transitive m n o mlten nlteo)

  reflexive Z      = LTEZero
  reflexive (S n)  = LTESucc (reflexive n)

Poset Nat LTE where
  antisymmetric Z Z LTEZero LTEZero = Refl
  antisymmetric (S n) (S m) (LTESucc mLTEn) (LTESucc nLTEm)
                with (antisymmetric n m mLTEn nLTEm)
    antisymmetric _ _ _ _ | Refl = Refl

decideLTE : (n, m : Nat) -> Dec (LTE n m)
decideLTE    Z      _  = Yes LTEZero
decideLTE (S _)     Z  = No  zeroNeverGreater where
  zeroNeverGreater : LTE (S _) Z -> Void
  zeroNeverGreater LTEZero     impossible
  zeroNeverGreater (LTESucc _) impossible
decideLTE (S x)   (S y) with (decEq (S x) (S y))
  | Yes eq      = rewrite eq in Yes (reflexive (S y))
  | No _ with (decideLTE x y)
    | Yes nLTEm = Yes (LTESucc nLTEm)
    | No  nGTm  = No (ltesuccinjective nGTm)
    where
      ltesuccinjective : (LTE n m -> Void) -> LTE (S n) (S m) -> Void
      ltesuccinjective disprf (LTESucc nLTEm) = void (disprf nLTEm)
      ltesuccinjective _ LTEZero impossible

Decidable [Nat, Nat] LTE where
  decide = decideLTE

lte : (m, n : Nat) -> Dec (LTE m n)
lte m n = decide {ts = [Nat, Nat]} {p = LTE} m n

shift : (m, n : Nat) -> LTE m n -> LTE (S m) (S n)
shift _ _ mLTEn = LTESucc mLTEn

Ordered Nat LTE where
  order Z      _ = Left LTEZero
  order _      Z = Right LTEZero
  order (S k) (S j) with (order {to=LTE} k j)
    order (S k) (S j) | Left  prf = Left  (shift k j prf)
    order (S k) (S j) | Right prf = Right (shift j k prf)

----------------------------------------------------------------------------------
---- Finite numbers
----------------------------------------------------------------------------------

using (k : Nat)
  data FinLTE : Fin k -> Fin k -> Type where
    FromNatPrf : LTE (finToNat m) (finToNat n) -> FinLTE m n

  Preorder (Fin k) FinLTE where
    transitive m n o (FromNatPrf p1) (FromNatPrf p2) =
      FromNatPrf (transitive (finToNat m) (finToNat n) (finToNat o) p1 p2)
    reflexive n = FromNatPrf (reflexive (finToNat n))

  Poset (Fin k) FinLTE where
    antisymmetric m n (FromNatPrf p1) (FromNatPrf p2) =
      finToNatInjective m n (antisymmetric (finToNat m) (finToNat n) p1 p2)

  Decidable [Fin k, Fin k] FinLTE where
    decide m n with (decideLTE (finToNat m) (finToNat n))
      | Yes prf    = Yes (FromNatPrf prf)
      | No  disprf = No (\(FromNatPrf prf) => disprf prf)

  Ordered (Fin k) FinLTE where
    order m n =
      either (Left . FromNatPrf)
             (Right . FromNatPrf)
             (order (finToNat m) (finToNat n))
