module prelude.cast

class Cast from to where
    cast : from -> to

-- String casts

instance Cast String Int where
    cast = prim__strToInt

instance Cast String Float where
    cast = prim__strToFloat

instance Cast String Integer where
    cast = prim__strToBigInt

-- Int casts

instance Cast Int String where
    cast = prim__intToStr

instance Cast Int Float where
    cast = prim__intToFloat

instance Cast Int Integer where
    cast = prim__intToBigInt 

instance Cast Int Char where
    cast = prim__intToChar

-- Float casts

instance Cast Float String where
    cast = prim__floatToStr

instance Cast Float Int where
    cast = prim__floatToInt

-- Integer casts

instance Cast Integer String where
    cast = prim__bigIntToStr

-- Char casts

instance Cast Char Int where
    cast = prim__charToInt


