module Control.Algebra.Laws

import Prelude.Algebra as A
import Control.Algebra as Alg
import Interfaces.Verified

%access export

-- Monoids

||| Inverses are unique.
uniqueInverse : VerifiedMonoid t => (x, y, z : t) ->
  y <+> x = A.neutral -> x <+> z = A.neutral -> y = z
uniqueInverse x y z p q =
  rewrite sym $ monoidNeutralIsNeutralL y in
    rewrite sym q in
      rewrite semigroupOpIsAssociative y x z in
  rewrite p in
    rewrite monoidNeutralIsNeutralR z in
      Refl

-- Groups

||| Only identity is self-squaring.
selfSquareId : VerifiedGroup t => (x : t) ->
  x <+> x = x -> x = A.neutral
selfSquareId x p =
  rewrite sym $ monoidNeutralIsNeutralR x in
    rewrite sym $ groupInverseIsInverseR x in
  rewrite sym $ semigroupOpIsAssociative (inverse x) x x in
    rewrite p in
      Refl

||| Inverse elements commute.
inverseCommute : VerifiedGroup t => (x, y : t) ->
  y <+> x = A.neutral -> x <+> y = A.neutral
inverseCommute x y p = selfSquareId (x <+> y) prop where
  prop : (x <+> y) <+> (x <+> y) = x <+> y
  prop =
    rewrite sym $ semigroupOpIsAssociative x y (x <+> y) in
      rewrite semigroupOpIsAssociative y x y in
    rewrite p in
      rewrite monoidNeutralIsNeutralR y in
        Refl

||| Every element has a right inverse.
groupInverseIsInverseL : VerifiedGroup t => (x : t) ->
  x <+> inverse x = Algebra.neutral
groupInverseIsInverseL x =
  inverseCommute x (inverse x) (groupInverseIsInverseR x)

||| -(-x) = x in any verified group.
inverseSquaredIsIdentity : VerifiedGroup t => (x : t) ->
  inverse (inverse x) = x
inverseSquaredIsIdentity x =
  let x' = inverse x in
    uniqueInverse
      x'
      (inverse x')
      x
      (groupInverseIsInverseR x')
      (groupInverseIsInverseR x)

||| If every square in a group is identity, the group is commutative.
squareIdCommutative : VerifiedGroup t => (x, y : t) ->
  ((a : t) -> a <+> a = A.neutral) ->
  x <+> y = y <+> x
squareIdCommutative x y p =
  let
    xy = x <+> y
    yx = y <+> x
      in
  uniqueInverse xy xy yx (p xy) prop where
    prop : (x <+> y) <+> (y <+> x) = A.neutral
    prop =
      rewrite sym $ semigroupOpIsAssociative x y (y <+> x) in
        rewrite semigroupOpIsAssociative y y x in
      rewrite p y in
        rewrite monoidNeutralIsNeutralR x in
          p x

||| -0 = 0 in any verified group.
inverseNeutralIsNeutral : VerifiedGroup t =>
  inverse (the t A.neutral) = A.neutral
inverseNeutralIsNeutral {t} =
  let e = the t neutral in
    rewrite sym $ cong {f = inverse} (groupInverseIsInverseL e) in
      rewrite monoidNeutralIsNeutralR $ inverse e in
        inverseSquaredIsIdentity e

||| -(x + y) = -y + -x in any verified group.
inverseOfSum : VerifiedGroup t => (l, r : t) ->
  inverse (l <+> r) = inverse r <+> inverse l
inverseOfSum {t} l r =
  let
    e = the t neutral
    il = inverse l
    ir = inverse r
    lr = l <+> r
    ilr = inverse lr
    iril = ir <+> il
    ile = il <+> e
      in
  -- expand
  rewrite sym $ monoidNeutralIsNeutralR ilr in
    rewrite sym $ groupInverseIsInverseR r in
      rewrite sym $ monoidNeutralIsNeutralL ir in
        rewrite sym $ groupInverseIsInverseR l in
  -- shuffle
  rewrite semigroupOpIsAssociative ir il l in
    rewrite sym $ semigroupOpIsAssociative iril l r in
      rewrite sym $ semigroupOpIsAssociative iril lr ilr in
  -- contract
  rewrite sym $ monoidNeutralIsNeutralL il in
    rewrite groupInverseIsInverseL lr in
      rewrite sym $ semigroupOpIsAssociative (ir <+> ile) l ile in
        rewrite semigroupOpIsAssociative l il e in
          rewrite groupInverseIsInverseL l in
            rewrite monoidNeutralIsNeutralL e in
              Refl

||| y = z if x + y = x + z.
cancelLeft : VerifiedGroup t => (x, y, z : t) ->
  x <+> y = x <+> z -> y = z
cancelLeft x y z p =
  rewrite sym $ monoidNeutralIsNeutralR y in
    rewrite sym $ groupInverseIsInverseR x in
      rewrite sym $ semigroupOpIsAssociative (inverse x) x y in
        rewrite p in
      rewrite semigroupOpIsAssociative (inverse x) x z in
    rewrite groupInverseIsInverseR x in
  monoidNeutralIsNeutralR z

||| y = z if y + x = z + x.
cancelRight : VerifiedGroup t => (x, y, z : t) ->
  y <+> x = z <+> x -> y = z
cancelRight x y z p =
  rewrite sym $ monoidNeutralIsNeutralL y in
    rewrite sym $ groupInverseIsInverseL x in
      rewrite semigroupOpIsAssociative y x (inverse x) in
        rewrite p in
      rewrite sym $ semigroupOpIsAssociative z x (inverse x) in
    rewrite groupInverseIsInverseL x in
  monoidNeutralIsNeutralL z

||| For any a and b, ax = b and ya = b have solutions.
latinSquareProperty : VerifiedGroup t => (a, b : t) ->
  ((x : t ** a <+> x = b),
    (y : t ** y <+> a = b))
latinSquareProperty a b =
  let a' = inverse a in
    (((a' <+> b) **
      rewrite semigroupOpIsAssociative a a' b in
        rewrite groupInverseIsInverseL a in
          monoidNeutralIsNeutralR b),
    (b <+> a' **
      rewrite sym $ semigroupOpIsAssociative b a' a in
        rewrite groupInverseIsInverseR a in
          monoidNeutralIsNeutralL b))

||| For any a, b, x, the solution to ax = b is unique.
uniqueSolutionR : VerifiedGroup t => (a, b, x, y : t) ->
  a <+> x = b -> a <+> y = b -> x = y
uniqueSolutionR a b x y p q = cancelLeft a x y $ trans p (sym q)

||| For any a, b, y, the solution to ya = b is unique.
uniqueSolutionL : VerifiedGroup t => (a, b, x, y : t) ->
  x <+> a = b -> y <+> a = b -> x = y
uniqueSolutionL a b x y p q = cancelRight a x y $ trans p (sym q)

||| -(x + y) = -x + -y in any verified abelian group.
inverseDistributesOverGroupOp : VerifiedAbelianGroup t => (l, r : t) ->
  inverse (l <+> r) = inverse l <+> inverse r
inverseDistributesOverGroupOp l r =
  rewrite abelianGroupOpIsCommutative (inverse l) (inverse r) in
    inverseOfSum l r

-- Rings

||| Anything multiplied by zero yields zero back in a verified ring.
multNeutralAbsorbingL : VerifiedRing t => (r : t) ->
  A.neutral <.> r = A.neutral
multNeutralAbsorbingL {t} r =
  let
    e = the t neutral
    ir = inverse r
    exr = e <.> r
    iexr = inverse exr
      in
  rewrite sym $ monoidNeutralIsNeutralR exr in
    rewrite sym $ groupInverseIsInverseR exr in
  rewrite sym $ semigroupOpIsAssociative iexr exr ((iexr <+> exr) <.> r) in
    rewrite groupInverseIsInverseR exr in
  rewrite sym $ ringOpIsDistributiveR e e r in
    rewrite monoidNeutralIsNeutralR e in
  groupInverseIsInverseR exr

||| Anything multiplied by zero yields zero back in a verified ring.
multNeutralAbsorbingR : VerifiedRing t => (l : t) ->
  l <.> A.neutral = A.neutral
multNeutralAbsorbingR {t} l =
  let
    e = the t neutral
    il = inverse l
    lxe = l <.> e
    ilxe = inverse lxe
      in
  rewrite sym $ monoidNeutralIsNeutralL lxe in
    rewrite sym $ groupInverseIsInverseL lxe in
  rewrite semigroupOpIsAssociative (l <.> (lxe <+> ilxe)) lxe ilxe in
    rewrite groupInverseIsInverseL lxe in
  rewrite sym $ ringOpIsDistributiveL l e e in
    rewrite monoidNeutralIsNeutralL e in
  groupInverseIsInverseL lxe

||| Inverse operator can be extracted before multiplication.
||| (-x)y = -(xy)
multInverseInversesL : VerifiedRing t => (l, r : t) ->
  inverse l <.> r = inverse (l <.> r)
multInverseInversesL l r =
  let
    il = inverse l
    lxr = l <.> r
    ilxr = il <.> r
    i_lxr = inverse lxr
      in
  rewrite sym $ monoidNeutralIsNeutralR ilxr in
    rewrite sym $ groupInverseIsInverseR lxr in
      rewrite sym $ semigroupOpIsAssociative i_lxr lxr ilxr in
  rewrite sym $ ringOpIsDistributiveR l il r in
    rewrite groupInverseIsInverseL l in
  rewrite multNeutralAbsorbingL r in
    monoidNeutralIsNeutralL i_lxr

||| Inverse operator can be extracted before multiplication.
||| x(-y) = -(xy)
multInverseInversesR : VerifiedRing t => (l, r : t) ->
  l <.> inverse r = inverse (l <.> r)
multInverseInversesR l r =
  let
    ir = inverse r
    lxr = l <.> r
    lxir = l <.> ir
    ilxr = inverse lxr
      in
  rewrite sym $ monoidNeutralIsNeutralL lxir in
    rewrite sym $ groupInverseIsInverseL lxr in
      rewrite semigroupOpIsAssociative lxir lxr ilxr in
  rewrite sym $ ringOpIsDistributiveL l ir r in
    rewrite groupInverseIsInverseR r in
  rewrite multNeutralAbsorbingR l in
    monoidNeutralIsNeutralR ilxr

||| Multiplication of inverses is the same as multiplication of
||| original elements.
||| (-x)(-y) = xy
multNegativeByNegativeIsPositive : VerifiedRing t => (l, r : t) ->
  inverse l <.> inverse r = l <.> r
multNegativeByNegativeIsPositive l r =
    rewrite multInverseInversesR (inverse l) r in
    rewrite sym $ multInverseInversesL (inverse l) r in
    rewrite inverseSquaredIsIdentity l in
    Refl

inverseOfUnityR : VerifiedRingWithUnity t => (x : t) ->
  inverse Alg.unity <.> x = inverse x
inverseOfUnityR x =
  rewrite multInverseInversesL Alg.unity x in
    rewrite ringWithUnityIsUnityR x in
      Refl

inverseOfUnityL : VerifiedRingWithUnity t => (x : t) ->
  x <.> inverse Alg.unity = inverse x
inverseOfUnityL x =
  rewrite multInverseInversesR x Alg.unity in
    rewrite ringWithUnityIsUnityL x in
      Refl
