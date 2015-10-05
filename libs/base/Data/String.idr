module Data.String

||| Convert a positive number string to a Num.
|||
||| ```idris example
||| parsePositive "123"
||| ```
||| ```idris example
||| parsePositive {a=Int} " +123"
||| ```
parsePositive : Num a => String -> Maybe a
parsePositive s = parsePosTrimmed (trim s) 
  where
    parsePosTrimmed s with (strM s)
      parsePosTrimmed ""             | StrNil         = Nothing
      parsePosTrimmed (strCons x xs) | (StrCons x xs) = 
        if (x == '+') 
          then map fromInteger (parsePosAux (unpack xs) 0)
          else map fromInteger (parsePosAux (unpack xs)  (cast (ord x - ord '0')))
            where
              parsePosAux : List Char -> Integer -> Maybe Integer
              parsePosAux []        acc = Just acc
              parsePosAux (c :: cs) acc = 
                if (c >= '0' && c <= '9') 
                  then parsePosAux cs ((acc * 10) + (cast ((ord c) - (ord '0'))))
                  else Nothing


||| Convert a number string to a Num.
|||
||| ```idris example
||| parseInteger " 123"
||| ```
||| ```idris example
||| parseInteger {a=Int} " -123"
||| ```
parseInteger : (Num a, Neg a) => String -> Maybe a
parseInteger s = parseIntTrimmed (trim s) 
  where
    parseIntTrimmed s with (strM s)
      parseIntTrimmed ""             | StrNil         = Nothing
      parseIntTrimmed (strCons x xs) | (StrCons x xs) = 
        if (x == '-') 
          then map (\y => negate (fromInteger y)) (parseIntegerAux (unpack xs) 0)
          else if (x == '+') 
            then map fromInteger (parseIntegerAux (unpack xs) (cast {from=Int} 0))
            else map fromInteger (parseIntegerAux (unpack xs) (cast (ord x - ord '0')))
              where
                parseIntegerAux : List Char -> Integer -> Maybe Integer
                parseIntegerAux []        acc = Just acc
                parseIntegerAux (c :: cs) acc = 
                  if (c >= '0' && c <= '9') 
                    then parseIntegerAux cs ((acc * 10) + (cast ((ord c) - (ord '0'))))
                    else Nothing
