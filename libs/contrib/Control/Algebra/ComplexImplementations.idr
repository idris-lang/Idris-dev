module Control.Algebra.ComplexImplementations

import Interfaces.Verified
import Data.Complex
import Control.Algebra
import Control.Algebra.Laws
import Control.Algebra.VectorSpace

%access public export
%default total

Semigroup a => Semigroup (Complex a) where
  (<+>) (a :+ b) (c :+ d) = (a <+> c) :+ (b <+> d)

Monoid a => Monoid (Complex a) where
  neutral = (neutral :+ neutral)

Group a => Group (Complex a) where
  inverse (r :+ i) = (inverse r :+ inverse i)

AbelianGroup a => AbelianGroup (Complex a) where {}

Ring a => Ring (Complex a) where
  (<.>) (a :+ b) (c :+ d) = (a <.> c <-> b <.> d) :+ (a <.> d <+> b <.> c)

RingWithUnity a => RingWithUnity (Complex a) where
  unity = (unity :+ neutral)

RingWithUnity a => Module a (Complex a) where
  (<#>) x = map (x <.>)

RingWithUnity a => InnerProductSpace a (Complex a) where
  (x :+ y) <||> z = realPart $ (x :+ inverse y) <.> z

----------------------------------------

VerifiedSemigroup a => VerifiedSemigroup (Complex a) where
  semigroupOpIsAssociative (a :+ x) (b :+ y) (c :+ z) =
    rewrite semigroupOpIsAssociative a b c in
      rewrite semigroupOpIsAssociative x y z in
        Refl

VerifiedMonoid t => VerifiedMonoid (Complex t) where
  monoidNeutralIsNeutralL (a :+ x) =
    rewrite monoidNeutralIsNeutralL a in
      rewrite monoidNeutralIsNeutralL x in
        Refl

  monoidNeutralIsNeutralR (a :+ x) =
    rewrite monoidNeutralIsNeutralR a in
      rewrite monoidNeutralIsNeutralR x in
        Refl

VerifiedGroup t => VerifiedGroup (Complex t) where
  groupInverseIsInverseR (r :+ i) =
    rewrite groupInverseIsInverseR r in
      rewrite groupInverseIsInverseR i in
        Refl

VerifiedAbelianGroup t => VerifiedAbelianGroup (Complex t) where
  abelianGroupOpIsCommutative (a :+ i) (b :+ j) =
    rewrite abelianGroupOpIsCommutative a b in
      rewrite abelianGroupOpIsCommutative i j in
        Refl

-- An interface resolution bug seems to make this impossible to prove.

-- https://github.com/idris-lang/Idris-dev/issues/4853
-- https://github.com/idris-lang/Idris2/issues/72

-- VerifiedRing t => VerifiedRing (Complex t) where
