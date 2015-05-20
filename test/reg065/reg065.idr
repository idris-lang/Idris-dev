||| Test that dependent type class definitions work.
|||
||| Fixes a regression where previous methods used in a later method's
||| type would lead to "can't resolve type class" errors
module TypeClassDep

import Data.Vect


class Foo a where
  getLen : Nat
  item : a -> Vect getLen a

instance Foo () where
  getLen  = 3
  item () = [(), (), ()]

instance Foo String where
  getLen = 1
  item str = [str]

check1 : item () = with Vect [(),(),()]
check1 = Refl

check2 : item "halløjsa" = with Vect ["halløjsa"]
check2 = Refl
