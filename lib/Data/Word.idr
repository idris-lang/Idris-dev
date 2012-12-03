module Data.Word

%access public

instance Num Word8 where
  (+) = prim__addW8
  (-) = prim__subW8
  (*) = prim__mulW8

  abs x = x
  fromInteger = prim__intToWord8

instance Num Word16 where
  (+) = prim__addW16
  (-) = prim__subW16
  (*) = prim__mulW16

  abs x = x
  fromInteger = prim__intToWord16
