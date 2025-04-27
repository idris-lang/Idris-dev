||| Ported from Haskell:
||| https://hackage.haskell.org/package/base-4.9.0.0/docs/src/Data.Monoid.html
module Data.Monoid

import Control.Algebra

%access public export
%default total

-- TODO: These instances exist, but can't be named the same.
-- Decide on names for these

Semigroup () where
  (<+>) _ _ = ()

VerifiedSemigroup () where
  semigroupOpIsAssociative _ _ _ = Refl

Monoid () where
  neutral = ()

VerifiedMonoid () where
  monoidNeutralIsNeutralL () = Refl
  monoidNeutralIsNeutralR () = Refl

-- Direct Products

(Semigroup m, Semigroup n) => Semigroup (m, n) where
  (a, b) <+> (c, d) = (a <+> c, b <+> d)

(VerifiedSemigroup m, VerifiedSemigroup n) => VerifiedSemigroup (m, n) where
  semigroupOpIsAssociative (a, x) (b, y) (c, z) =
    rewrite semigroupOpIsAssociative a b c in
      rewrite semigroupOpIsAssociative x y z in
        Refl

(Monoid m, Monoid n) => Monoid (m, n) where
  neutral = (neutral, neutral)

(VerifiedMonoid m, VerifiedMonoid n) => VerifiedMonoid (m, n) where
  monoidNeutralIsNeutralL (a, b) =
    rewrite monoidNeutralIsNeutralL a in
      rewrite monoidNeutralIsNeutralL b in
        Refl

  monoidNeutralIsNeutralR (a, b) =
    rewrite monoidNeutralIsNeutralR a in
      rewrite monoidNeutralIsNeutralR b in
        Refl

(Group g, Group h) => Group (g, h) where
  inverse (a, b) = (inverse a, inverse b)

(VerifiedGroup g, VerifiedGroup h) => VerifiedGroup (g, h) where
  groupInverseIsInverseR (a, b) =
    rewrite groupInverseIsInverseR a in
      rewrite groupInverseIsInverseR b in
        Refl

(AbelianGroup g, AbelianGroup h) => AbelianGroup (g, h) where
  abelianGroupOpIsCommutative (a, b) (c, d) =
    rewrite abelianGroupOpIsCommutative a c in
      rewrite abelianGroupOpIsCommutative b d in
        Refl

(Ring r, Ring s) => Ring (r, s) where
  (<.>) (a, b) (c, d) = ((a <.> c), (b <.> d))

(VerifiedRing r, VerifiedRing s) => VerifiedRing (r, s) where
  ringOpIsAssociative (a, b) (c, d) (e, f) =
    rewrite ringOpIsAssociative a c e in
      rewrite ringOpIsAssociative b d f in
        Refl

  ringOpIsDistributiveL (a, b) (c, d) (e, f) =
    rewrite ringOpIsDistributiveL a c e in
      rewrite ringOpIsDistributiveL b d f in
        Refl

  ringOpIsDistributiveR (a, b) (c, d) (e, f) =
    rewrite ringOpIsDistributiveR a c e in
      rewrite ringOpIsDistributiveR b d f in
        Refl
