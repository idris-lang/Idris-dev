module Data.Bits

%access public
%default partial

infixl 5 .|.
infixl 7 .&.

class Num a => Bits a where
  (.|.) : a -> a -> a
  (.&.) : a -> a -> a

  xor : a -> a -> a
  complement : a -> a
  shiftL : a -> Int -> a
  shiftR : a -> Int -> a

instance Bits Int where
  (.|.) = prim__orInt
  (.&.) = prim__andInt

  xor = prim__xorInt
  complement = prim__complInt
  shiftL = prim__shLInt
  shiftR = prim__shRInt
