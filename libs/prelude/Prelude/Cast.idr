module Prelude.Cast

import Prelude.Bool
import public Builtins

||| Interface for transforming an instance of a data type to another type.
interface Cast from to where
    ||| Perform a cast operation.
    |||
    ||| @orig The original type.
    cast : (orig : from) -> to

-- String casts

implementation Cast String Int where
    cast = prim__fromStrInt

implementation Cast String Double where
    cast = prim__strToFloat

implementation Cast String Integer where
    cast = prim__fromStrBigInt

-- Int casts

implementation Cast Int String where
    cast = prim__toStrInt

implementation Cast Int Double where
    cast = prim__toFloatInt

implementation Cast Int Integer where
    cast = prim__sextInt_BigInt

-- Double casts

implementation Cast Double String where
    cast = prim__floatToStr

implementation Cast Double Int where
    cast = prim__fromFloatInt

implementation Cast Double Integer where
    cast = prim__fromFloatBigInt

-- Integer casts

implementation Cast Integer String where
    cast = prim__toStrBigInt

implementation Cast Integer Double where
    cast = prim__toFloatBigInt

-- Char casts

implementation Cast Char Int where
    cast = prim__charToInt
