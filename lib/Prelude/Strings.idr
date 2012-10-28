module Prelude.Strings

import Builtins
import Prelude.List
import Prelude.Chars
import Prelude.Cast

-- Some more complex string operations

data StrM : String -> Set where
    StrNil : StrM ""
    StrCons : (x : Char) -> (xs : String) -> StrM (strCons x xs)

%assert_total
strHead' : (x : String) -> so (not (x == "")) -> Char
strHead' x p = prim__strHead x

%assert_total
strTail' : (x : String) -> so (not (x == "")) -> String
strTail' x p = prim__strTail x

-- we need the 'believe_me' because the operations are primitives

%assert_total
strM : (x : String) -> StrM x
strM x with (choose (not (x == "")))
  strM x | (Left p)  = believe_me $ StrCons (strHead' x p) (strTail' x p)
  strM x | (Right p) = believe_me StrNil

unpack : String -> List Char
unpack s with (strM s)
  unpack ""             | StrNil = []
  unpack (strCons x xs) | (StrCons _ _) = x :: unpack xs

pack : List Char -> String
pack [] = ""
pack (x :: xs) = strCons x (pack xs)

instance Cast String (List Char) where
    cast = unpack

instance Cast (List Char) String where
    cast = pack

span : (Char -> Bool) -> String -> (String, String)
span p xs with (strM xs)
  span p ""             | StrNil        = ("", "")
  span p (strCons x xs) | (StrCons _ _) with (p x)
    | True with (span p xs)
      | (ys, zs) = (strCons x ys, zs)
    | False = ("", strCons x xs)

break : (Char -> Bool) -> String -> (String, String)
break p = span (not . p)

split : (Char -> Bool) -> String -> List String
split p xs = map pack (split p (unpack xs))

ltrim : String -> String
ltrim xs with (strM xs)
    ltrim "" | StrNil = ""
    ltrim (strCons x xs) | StrCons _ _
        = if (isSpace x) then (ltrim xs) else (strCons x xs)

trim : String -> String
trim xs = ltrim (reverse (ltrim (reverse xs)))

words' : List Char -> List (List Char)
words' s = case dropWhile isSpace s of
            [] => []
            s' => let (w, s'') = break isSpace s'
                  in w :: words' s''

words : String -> List String
words s = map pack $ words' $ unpack s

partial
foldr1 : (a -> a -> a) -> List a -> a	
foldr1 f [x] = x
foldr1 f (x::xs) = f x (foldr1 f xs)

%assert_total -- due to foldr1, but used safely
unwords' : List (List Char) -> List Char
unwords' [] = []                         
unwords' ws = (foldr1 addSpace ws)
        where
            addSpace : List Char -> List Char -> List Char
            addSpace w s = w ++ (' ' :: s) 
          
unwords : List String -> String
unwords = pack . unwords' . map unpack

