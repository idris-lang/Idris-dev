module Control.Algebra.Laws

import Prelude.Algebra as A
import Control.Algebra
import Interfaces.Verified

%access export

||| -(-x) = x in any verified group.
inverseSquaredIsIdentity : VerifiedGroup t => (x : t) ->
  inverse (inverse x) = x
inverseSquaredIsIdentity x =
  let
    ix = inverse x
    iix = inverse ix
      in
  rewrite sym $ monoidNeutralIsNeutralR iix in
    rewrite sym $ groupInverseIsInverseL x in
      rewrite sym $ semigroupOpIsAssociative x ix iix in
    rewrite groupInverseIsInverseL ix in
  monoidNeutralIsNeutralL x

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
    sum = l <+> r
    ilr = inverse sum
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
      rewrite sym $ semigroupOpIsAssociative iril sum ilr in
  -- contract
  rewrite sym $ monoidNeutralIsNeutralL il in
    rewrite groupInverseIsInverseL sum in
      rewrite sym $ semigroupOpIsAssociative (ir <+> ile) l ile in
        rewrite semigroupOpIsAssociative l il e in
          rewrite groupInverseIsInverseL l in
            rewrite monoidNeutralIsNeutralL e in
              Refl

||| -(x + y) = -x + -y in any verified abelian group.
inverseDistributesOverGroupOp : VerifiedAbelianGroup t => (l, r : t) ->
  inverse (l <+> r) = inverse l <+> inverse r
inverseDistributesOverGroupOp l r =
  rewrite abelianGroupOpIsCommutative (inverse l) (inverse r) in
    inverseOfSum l r

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
