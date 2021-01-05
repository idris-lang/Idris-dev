import Prelude.Algebra as A
import Control.Algebra
import Control.Algebra.Laws

%access public export

||| A homomorphism is a mapping that preserves group structure.
interface (VerifiedGroup a, VerifiedGroup b) => GroupHomomorphism a b where
  to : a -> b
  toGroup : (x, y : a) ->
    to (x <+> y) = (to x) <+> (to y)

||| Homomorphism preserves neutral.
homoNeutral : GroupHomomorphism a b =>
  to (the a A.neutral) = the b A.neutral
homoNeutral {a} =
  let ae = the a A.neutral in
    selfSquareId (to ae) $
      trans (sym $ toGroup ae ae) $
        cong {f = to} $ monoidNeutralIsNeutralL ae

||| Homomorphism preserves inverses.
homoInverse : GroupHomomorphism a b => (x : a) ->
  the b (to $ inverse x) = the b (inverse $ to x)
homoInverse {a} {b} x =
  cancelRight (to x) (to $ inverse x) (inverse $ to x) $
    trans (sym $ toGroup (inverse x) x) $
      trans (cong {f = to} $ groupInverseIsInverseR x) $
        trans (homoNeutral {a=a} {b=b}) $
          sym $ groupInverseIsInverseR (to x)
