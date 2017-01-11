||| Test some deriving features
module Deriving

%language ElabReflection

-- NB: test disabled due to excess memory consumption

import Pruviloj
import Pruviloj.Derive.DecEq

data Vect : Nat -> Type -> Type where
  Nil : Vect Z a
  (::) : a -> Vect n a -> Vect (S n) a

total
decVectEq : DecEq a => (xs, ys : Vect n a) -> Dec (xs = ys)
%runElab (deriveDecEq `{decVectEq})

implementation DecEq a => DecEq (Vect n a) where
  decEq xs ys = decVectEq xs ys

forgetProof : Dec a -> Bool
forgetProof (Yes _) = True
forgetProof (No _) = False

test1 : (xs, ys : Vect n Nat) -> Bool
test1 xs ys with (decEq xs ys)
  test1 xs xs | Yes Refl = True
  test1 xs ys | No _     = False



-- Local Variables:
-- idris-load-packages: ("pruviloj")
-- End:
