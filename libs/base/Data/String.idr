module Data.String
%access public export

private
parseNumWithoutSign : List Char -> Integer -> Maybe Integer
parseNumWithoutSign []        acc = Just acc
parseNumWithoutSign (c :: cs) acc = 
  if (c >= '0' && c <= '9') 
  then parseNumWithoutSign cs ((acc * 10) + (cast ((ord c) - (ord '0'))))
  else Nothing
         

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
      parsePosTrimmed (strCons '+' xs) | (StrCons '+' xs) = 
        map fromInteger (parseNumWithoutSign (unpack xs) 0)
      parsePosTrimmed (strCons x xs) | (StrCons x xs) = 
        if (x >= '0' && x <= '9') 
        then  map fromInteger (parseNumWithoutSign (unpack xs)  (cast (ord x - ord '0')))
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
          then map (\y => negate (fromInteger y)) (parseNumWithoutSign (unpack xs) 0)
          else if (x == '+') 
            then map fromInteger (parseNumWithoutSign (unpack xs) (cast {from=Int} 0))
            else map fromInteger (parseNumWithoutSign (unpack xs) (cast (ord x - ord '0')))


||| Convert a number string to a Double.
|||
||| ```idris example
||| parseDouble "+123.123e-2"
||| ```
||| ```idris example
||| parseDouble {a=Int} " -123.123E+2"
||| ```
||| ```idris example
||| parseDouble {a=Int} " +123.123"
||| ```
parseDouble : String -> Maybe Double
parseDouble = mkDouble . wfe . trim
  where
    mkDouble (Just (w, f, e)) = let ex = intPow 10 e in
                                Just $ (w * ex + f * ex)
    mkDouble Nothing = Nothing
    
    intPow : Integer -> Integer -> Double
    intPow base exp = assert_total $ if exp > 0 then (num base exp) else 1 / (num base exp)
      where
        num base 0 = 1
        num base e = if e < 0 
                     then cast base * num base (e + 1)
                     else cast base * num base (e - 1)

    wfe : String -> Maybe (Double, Double, Integer)
    wfe cs = case split (== '.') cs of
               (wholeAndExp :: []) => 
                 case split (\c => c == 'e' || c == 'E') wholeAndExp of
                   (whole::exp::[]) =>  
                     do
                       w <- cast <$> parseInteger whole
                       e <- parseInteger exp
                       pure (w, 0, e)
                   (whole::[]) =>      
                     do
                       w <- cast <$> parseInteger whole
                       pure (w, 0, 0)
                   _ => Nothing
               (whole::fracAndExp::[]) =>
                 case split (\c => c == 'e' || c == 'E') fracAndExp of
                   (""::exp::[]) => Nothing
                   (frac::exp::[]) =>  
                     do
                       w <- cast <$> parseInteger whole
                       f <- (/ (pow 10 (length frac))) <$> 
                            (cast <$> parseNumWithoutSign (unpack frac) 0)
                       e <- parseInteger exp
                       pure (w, if w < 0 then (-f) else f, e)
                   (frac::[]) =>      
                     do
                       w <- cast <$> parseInteger whole
                       f <- (/ (pow 10 (length frac))) <$> 
                            (cast <$> parseNumWithoutSign (unpack frac) 0)
                       pure (w, if w < 0 then (-f) else f, 0)
                   _ => Nothing
               _ => Nothing
