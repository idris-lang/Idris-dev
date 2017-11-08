module Test

LTE : (x, y : Double) -> Type

NonNegDouble : Type
NonNegDouble = Subset Double (\ x => 0.0 `LTE` x)

plus : (x, y : NonNegDouble) -> NonNegDouble

mult : (x, y : NonNegDouble) -> NonNegDouble

fromIntegerNN : Integer -> NonNegDouble

implementation [numnnd] Num NonNegDouble where
  (+) = plus
  (*) = mult
  fromInteger = fromIntegerNN

using implementation numnnd
  x : NonNegDouble
  y : NonNegDouble
  z : NonNegDouble
  z = x + y

