module Prelude.Cast

class Cast from to where
    cast : from -> to

-- String casts

instance Cast String Int where
    cast = prim__fromStrInt

instance Cast String Float where
    cast = prim__strToFloat

instance Cast String Integer where
    cast = prim__fromStrBigInt

-- Int casts

instance Cast Int String where
    cast = prim__toStrInt

instance Cast Int Float where
    cast = prim__toFloatInt

instance Cast Int Integer where
    cast = prim__sextInt_BigInt

instance Cast Int Char where
    cast = prim__intToChar

-- Float casts

instance Cast Float String where
    cast = prim__floatToStr

instance Cast Float Int where
    cast = prim__fromFloatInt

-- Integer casts

instance Cast Integer String where
    cast = prim__toStrBigInt

-- Char casts

instance Cast Char Int where
    cast = prim__charToInt


