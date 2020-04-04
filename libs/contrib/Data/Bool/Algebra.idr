module Data.Bool.Algebra

import Control.Algebra
import Interfaces.Verified

%access public export
%default total

-- && is Bool -> Lazy Bool -> Bool,
-- but Bool -> Bool -> Bool is required
and : Bool -> Bool -> Bool
and True True = True
and _ _ = False

xor : Bool -> Bool -> Bool
xor True True = False
xor False False = False
xor _ _ = True

[PlusBoolSemi] Semigroup Bool where
  (<+>) = xor

[PlusBoolSemiV] VerifiedSemigroup Bool using PlusBoolSemi where
  semigroupOpIsAssociative True True True = Refl
  semigroupOpIsAssociative True True False = Refl
  semigroupOpIsAssociative True False True = Refl
  semigroupOpIsAssociative True False False = Refl
  semigroupOpIsAssociative False True True = Refl
  semigroupOpIsAssociative False False True = Refl
  semigroupOpIsAssociative False True False = Refl
  semigroupOpIsAssociative False False False = Refl

[PlusBoolMonoid] Monoid Bool using PlusBoolSemi where
  neutral = False

[PlusBoolMonoidV] VerifiedMonoid Bool using PlusBoolSemiV, PlusBoolMonoid where
  monoidNeutralIsNeutralL True = Refl
  monoidNeutralIsNeutralL False = Refl

  monoidNeutralIsNeutralR True = Refl
  monoidNeutralIsNeutralR False = Refl

[PlusBoolGroup] Group Bool using PlusBoolMonoid where
  -- Each Bool is its own additive inverse.
  inverse = id

[PlusBoolGroupV] VerifiedGroup Bool using PlusBoolMonoidV, PlusBoolGroup where
  groupInverseIsInverseR True = Refl
  groupInverseIsInverseR False = Refl

[PlusBoolAbel] AbelianGroup Bool using PlusBoolGroup where

[PlusBoolAbelV] VerifiedAbelianGroup Bool using PlusBoolGroupV, PlusBoolAbel where
  abelianGroupOpIsCommutative True True = Refl
  abelianGroupOpIsCommutative True False = Refl
  abelianGroupOpIsCommutative False True = Refl
  abelianGroupOpIsCommutative False False = Refl

[RingBool] Ring Bool using PlusBoolAbel where
  (<.>) = and

[RingBoolV] VerifiedRing Bool using RingBool, PlusBoolAbelV where
  ringOpIsAssociative True True True = Refl
  ringOpIsAssociative True True False = Refl
  ringOpIsAssociative True False True = Refl
  ringOpIsAssociative True False False = Refl
  ringOpIsAssociative False True True = Refl
  ringOpIsAssociative False False True = Refl
  ringOpIsAssociative False True False = Refl
  ringOpIsAssociative False False False = Refl

  ringOpIsDistributiveL True True True = Refl
  ringOpIsDistributiveL True True False = Refl
  ringOpIsDistributiveL True False True = Refl
  ringOpIsDistributiveL True False False = Refl
  ringOpIsDistributiveL False True True = Refl
  ringOpIsDistributiveL False False True = Refl
  ringOpIsDistributiveL False True False = Refl
  ringOpIsDistributiveL False False False = Refl

  ringOpIsDistributiveR True True True = Refl
  ringOpIsDistributiveR True True False = Refl
  ringOpIsDistributiveR True False True = Refl
  ringOpIsDistributiveR True False False = Refl
  ringOpIsDistributiveR False True True = Refl
  ringOpIsDistributiveR False False True = Refl
  ringOpIsDistributiveR False True False = Refl
  ringOpIsDistributiveR False False False = Refl

[RingUnBool] RingWithUnity Bool using RingBool where
  unity = True

VerifiedRingWithUnity Bool using RingUnBool, RingBoolV where
  ringWithUnityIsUnityL True = Refl
  ringWithUnityIsUnityL False = Refl

  ringWithUnityIsUnityR True = Refl
  ringWithUnityIsUnityR False = Refl
