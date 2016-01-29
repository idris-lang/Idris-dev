module Prelude.Cast

import Prelude.Bool
import public Builtins

%access public export

||| Interface for transforming an instance of a data type to another type.
interface Cast from to where
    ||| Perform a cast operation.
    |||
    ||| @orig The original type.
    cast : (orig : from) -> to

-- String casts

Cast String Int where
    cast = prim__fromStrInt

Cast String Double where
    cast = prim__strToFloat

Cast String Integer where
    cast = prim__fromStrBigInt

-- Int casts

Cast Int String where
    cast = prim__toStrInt

Cast Int Double where
    cast = prim__toFloatInt

Cast Int Integer where
    cast = prim__sextInt_BigInt

-- Double casts

Cast Double String where
    cast = prim__floatToStr

Cast Double Int where
    cast = prim__fromFloatInt

Cast Double Integer where
    cast = prim__fromFloatBigInt

-- Integer casts

Cast Integer String where
    cast = prim__toStrBigInt

Cast Integer Double where
    cast = prim__toFloatBigInt

-- Char casts

Cast Char Int where
    cast = prim__charToInt
