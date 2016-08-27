||| Test that dependent type interface definitions work.
|||
||| Fixes a regression where previous methods used in a later method's
||| type would lead to "can't find interface" errors
module InterfaceDep

import Data.Vect


interface Foo a where
  getLen : Nat
  item : a -> Vect getLen a

implementation Foo () where
  getLen  = 3
  item () = [(), (), ()]

implementation Foo String where
  getLen = 1
  item str = [str]

check1 : item () = with Vect [(),(),()]
check1 = Refl

check2 : item "halløjsa" = with Vect ["halløjsa"]
check2 = Refl
