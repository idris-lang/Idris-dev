module Data.Bool.Algebra

import Control.Algebra
import Control.Algebra.CyclicGroup
import Data.ZZ

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

Semigroup Bool where
  (<+>) = xor

VerifiedSemigroup Bool where
  semigroupOpIsAssociative True True True = Refl
  semigroupOpIsAssociative True True False = Refl
  semigroupOpIsAssociative True False True = Refl
  semigroupOpIsAssociative True False False = Refl
  semigroupOpIsAssociative False True True = Refl
  semigroupOpIsAssociative False False True = Refl
  semigroupOpIsAssociative False True False = Refl
  semigroupOpIsAssociative False False False = Refl

Monoid Bool where
  neutral = False

VerifiedMonoid Bool where
  monoidNeutralIsNeutralL True = Refl
  monoidNeutralIsNeutralL False = Refl

  monoidNeutralIsNeutralR True = Refl
  monoidNeutralIsNeutralR False = Refl

Group Bool where
  -- Each Bool is its own additive inverse.
  inverse = id

VerifiedGroup Bool where
  groupInverseIsInverseR True = Refl
  groupInverseIsInverseR False = Refl

CyclicGroup Bool where
  generator = (True ** \x =>
    case x of
      True => (1 ** Refl)
      False => (0 ** Refl))

Ring Bool where
  (<.>) = and

VerifiedRing Bool where
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

RingWithUnity Bool where
  unity = True

VerifiedRingWithUnity Bool where
  ringWithUnityIsUnityL True = Refl
  ringWithUnityIsUnityL False = Refl

  ringWithUnityIsUnityR True = Refl
  ringWithUnityIsUnityR False = Refl
