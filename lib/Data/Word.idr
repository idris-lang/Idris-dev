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

instance Num Word32 where
  (+) = prim__addW32
  (-) = prim__subW32
  (*) = prim__mulW32

  abs x = x
  fromInteger = prim__intToWord32

