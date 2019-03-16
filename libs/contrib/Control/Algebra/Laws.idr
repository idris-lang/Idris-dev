module Control.Algebra.Laws

import Prelude.Algebra as A
import Control.Algebra
import Interfaces.Verified

%access export

||| A prof that -0 = 0 in any verified group.
inverseNeutralIsNeutral : VerifiedGroup t => inverse (the t A.neutral) = A.neutral
inverseNeutralIsNeutral {t} =
    let zero = the t neutral
        step1 = cong {f = (<+> inverse zero)} (the (zero = zero) Refl)
        step2 = replace {P = \x => zero <+> inverse zero = x} (groupInverseIsInverseL zero) step1
    in
    replace {P = \x => x = neutral} (monoidNeutralIsNeutralR $ inverse zero) step2

||| A proof that -(-x) = x in any verified group.
inverseSquaredIsIdentity : VerifiedGroup t => (x : t) -> inverse (inverse x) = x
inverseSquaredIsIdentity {t} x =
    let zero = the t neutral
        step1 = cong {f = (x <+>)} (groupInverseIsInverseL (inverse x))
        step2 = replace {P = \r => r = x <+> neutral} (semigroupOpIsAssociative x (inverse x) (inverse $ inverse x)) step1
        step3 = replace {P = \r => r <+> inverse (inverse x) = x <+> neutral} (groupInverseIsInverseL x) step2
        step4 = replace {P = \r => r = x <+> neutral} (monoidNeutralIsNeutralR (inverse $ inverse x)) step3
    in
    replace {P = \r => inverse (inverse x) = r} (monoidNeutralIsNeutralL x) step4

||| A proof that -(x + y) = -x - y in any verified abelian group.
inverseDistributesOverGroupOp : VerifiedAbelianGroup t => (l, r : t) -> inverse (l <+> r) = inverse l <+> inverse r
inverseDistributesOverGroupOp {t} l r =
    let step1 = replace {P = \x => x = neutral} (sym $ groupInverseIsInverseL (l <+> r)) $ the (the t neutral = neutral) Refl
        step2 = cong {f = ((inverse r) <+>) . ((inverse l) <+>)} step1
        step3 = replace {P = \x => inverse r <+> (inverse l <+> (l <+> r <+> inverse (l <+> r))) = inverse r <+> x} (monoidNeutralIsNeutralL (inverse l)) step2
        step4 = replace {P = \x => x = inverse r <+> inverse l} (semigroupOpIsAssociative (inverse r) (inverse l) (l <+> r <+> inverse (l <+> r))) step3
        step5 = replace {P = \x => x = inverse r <+> inverse l} (semigroupOpIsAssociative (inverse r <+> inverse l) (l <+> r) (inverse (l <+> r))) step4
        step6 = replace {P = \x => x <+> inverse (l <+> r) = inverse r <+> inverse l} (semigroupOpIsAssociative (inverse r <+> inverse l) l r) step5
        step7 = replace {P = \x => x <+> r <+> inverse (l <+> r) = inverse r <+> inverse l} (sym $ semigroupOpIsAssociative (inverse r) (inverse l) l) step6
        step8 = replace {P = \x => inverse r <+> x <+> r <+> inverse (l <+> r) = inverse r <+> inverse l} (groupInverseIsInverseR l) step7
        step9 = replace {P = \x => x <+> r <+> inverse (l <+> r) = inverse r <+> inverse l} (monoidNeutralIsNeutralL (inverse r)) step8
        step10 = replace {P = \x => x <+> inverse (l <+> r) = inverse r <+> inverse l} (groupInverseIsInverseR r) step9
        step11 = replace {P = \x => x = inverse r <+> inverse l} (monoidNeutralIsNeutralR (inverse (l <+> r))) step10
    in
    replace {P = \x => inverse (l <+> r) = x} (abelianGroupOpIsCommutative (inverse r) (inverse l)) step11

||| A proof that anything multiplied by zero yields zero back.
multNeutralAbsorbingL : VerifiedRingWithUnity t => (r : t) -> A.neutral <.> r = A.neutral
multNeutralAbsorbingL r =
    let step1 = the (unity <.> r = r) (ringWithUnityIsUnityR r)
        step2 = replace {P = \x => x <.> r = r} (sym $ monoidNeutralIsNeutralR unity) step1
        step3 = replace {P = \x => x = r} (ringOpIsDistributiveR neutral unity r) step2
        step4 = replace {P = \x => neutral <.> r <+> x = r} (ringWithUnityIsUnityR r) step3
        step5 = cong {f = \x => x <+> inverse r} step4
        step6 = replace {P = \x => x = r <+> inverse r} (sym $ semigroupOpIsAssociative (neutral <.> r) r (inverse r)) step5
        step7 = replace {P = \x => neutral <.> r <+> x = x} (groupInverseIsInverseL r) step6
    in
    replace {P = \x => x = neutral} (monoidNeutralIsNeutralL (neutral <.> r)) step7

||| A proof that anything multiplied by zero yields zero back.
multNeutralAbsorbingR : VerifiedRingWithUnity t => (l : t) -> l <.> A.neutral = A.neutral
multNeutralAbsorbingR l =
    let step1 = the (l <.> unity = l) (ringWithUnityIsUnityL l)
        step2 = replace {P = \x => l <.> x = l} (sym $ monoidNeutralIsNeutralR unity) step1
        step3 = replace {P = \x => x = l} (ringOpIsDistributiveL l neutral unity) step2
        step4 = replace {P = \x => l <.> neutral <+> x = l} (ringWithUnityIsUnityL l) step3
        step5 = cong {f = \x => x <+> inverse l} step4
        step6 = replace {P = \x => x = l <+> inverse l} (sym $ semigroupOpIsAssociative (l <.> neutral) l (inverse l)) step5
        step7 = replace {P = \x => l <.> neutral <+> x = x} (groupInverseIsInverseL l) step6
    in
    replace {P = \x => x = neutral} (monoidNeutralIsNeutralL (l <.> neutral)) step7

||| A proof that inverse operator can be extracted before multiplication
||| (-x)y = -(xy)
multInverseInversesL : VerifiedRingWithUnity t => (l, r : t) -> inverse l <.> r = inverse (l <.> r)
multInverseInversesL l r =
    let step1 = replace {P = \x => x <.> r = neutral} (sym $ groupInverseIsInverseL l) (multNeutralAbsorbingL r)
        step2 = replace {P = \x => x = neutral} (ringOpIsDistributiveR l (inverse l) r) step1
        step3 = cong {f = ((inverse (l <.> r)) <+>)} step2
        step4 = replace {P = \x => inverse (l <.> r) <+> (l <.> r <+> inverse l <.> r) = x} (monoidNeutralIsNeutralL (inverse (l <.> r))) step3
        step5 = replace {P = \x => x = inverse (l <.> r)} (semigroupOpIsAssociative (inverse (l <.> r)) (l <.> r) (inverse l <.> r)) step4
        step6 = replace {P = \x => x <+> inverse l <.> r = inverse (l <.> r)} (groupInverseIsInverseR (l <.> r)) step5
    in
    replace {P = \x => x = inverse (l <.> r)} (monoidNeutralIsNeutralR (inverse l <.> r)) step6

||| A proof that inverse operator can be extracted before multiplication
||| x(-y) = -(xy)
multInverseInversesR : VerifiedRingWithUnity t => (l, r : t) -> l <.> inverse r = inverse (l <.> r)
multInverseInversesR l r =
    let step1 = replace {P = \x => l <.> x = neutral} (sym $ groupInverseIsInverseL r) (multNeutralAbsorbingR l)
        step2 = replace {P = \x => x = neutral} (ringOpIsDistributiveL l r (inverse r)) step1
        step3 = cong {f = ((inverse (l <.> r)) <+>)} step2
        step4 = replace {P = \x => inverse (l <.> r) <+> (l <.> r <+> l <.> inverse r) = x} (monoidNeutralIsNeutralL (inverse (l <.> r))) step3
        step5 = replace {P = \x => x = inverse (l <.> r)} (semigroupOpIsAssociative (inverse (l <.> r)) (l <.> r) (l <.> inverse r)) step4
        step6 = replace {P = \x => x <+> l <.> inverse r = inverse (l <.> r)} (groupInverseIsInverseR (l <.> r)) step5
    in
    replace {P = \x => x = inverse (l <.> r)} (monoidNeutralIsNeutralR (l <.> inverse r)) step6

||| A proof that multiplication of inverses is the same as multiplication of original
||| elements. (-x)(-y) = xy
multNegativeByNegativeIsPositive : VerifiedRingWithUnity t => (l, r : t) -> inverse l <.> inverse r = l <.> r
multNegativeByNegativeIsPositive l r =
    rewrite multInverseInversesR (inverse l) r in
    rewrite sym $ multInverseInversesL (inverse l) r in
    rewrite inverseSquaredIsIdentity l in
    Refl
