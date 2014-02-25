module Prelude.Cast

class Cast from to where
    cast : from -> to

-- String casts

instance Cast String Int where
    cast = prim__fromStrInt

instance Cast String Float64 where
    cast = prim__strToFloat64

instance Cast String Integer where
    cast = prim__fromStrBigInt

-- Int casts

instance Cast Int String where
    cast = prim__toStrInt

instance Cast Int Float64 where
    cast = prim__toFloat64Int

instance Cast Int Integer where
    cast = prim__sextInt_BigInt

instance Cast Int Char where
    cast = prim__intToChar

-- Float64 casts

instance Cast Float64 String where
    cast = prim__float64ToStr

instance Cast Float64 Int where
    cast = prim__fromFloat64Int
-- note, really should be Float64 -> Int64 to always make sense

-- Integer casts

instance Cast Integer String where
    cast = prim__toStrBigInt

-- Char casts

instance Cast Char Int where
    cast = prim__charToInt


