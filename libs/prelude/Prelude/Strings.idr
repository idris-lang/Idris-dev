module Prelude.Strings

import Builtins
import Prelude.List
import Prelude.Chars
import Prelude.Cast
import Prelude.Either
import Prelude.Foldable

-- | Appends two strings together.
(++) : String -> String -> String
(++) = prim__concat

-- | Returns the first character in the specified string.
partial
strHead : String -> Char
strHead = prim__strHead

-- | Returns the characters specified after the head of the string.
partial
strTail : String -> String
strTail = prim__strTail

-- | Adds a character to the from of the specified string.
strCons : Char -> String -> String
strCons = prim__strCons

-- | Returns the nth character (starting from 0) of the specified string.
partial
strIndex : String -> Int -> Char
strIndex = prim__strIndex

-- | Reverses the elements within a String.
reverse : String -> String
reverse = prim__strRev

null : Ptr
null = prim__null

-- Some more complex string operations

data StrM : String -> Type where
    StrNil : StrM ""
    StrCons : (x : Char) -> (xs : String) -> StrM (strCons x xs)

strHead' : (x : String) -> so (not (x == "")) -> Char
strHead' x p = assert_total $ prim__strHead x

strTail' : (x : String) -> so (not (x == "")) -> String
strTail' x p = assert_total $ prim__strTail x

-- we need the 'believe_me' because the operations are primitives
strM : (x : String) -> StrM x
strM x with (choose (not (x == "")))
  strM x | (Left p)  = really_believe_me $ 
                           StrCons (assert_total (strHead' x p))
                                   (assert_total (strTail' x p))
  strM x | (Right p) = really_believe_me StrNil

-- annoyingly, we need these assert_totals because StrCons doesn't have
-- a recursive argument, therefore the termination checker doesn't believe
-- the string is guaranteed smaller. It makes a good point.

unpack : String -> List Char
unpack s with (strM s)
  unpack ""             | StrNil = []
  unpack (strCons x xs) | (StrCons x xs) = x :: assert_total (unpack xs)

pack : (Foldable t) => t Char -> String
pack = foldr strCons ""

singleton : Char -> String
singleton c = strCons c ""

instance Cast String (List Char) where
  cast = unpack

instance Cast (List Char) String where
  cast = pack

instance Cast Char String where
  cast = singleton

instance Semigroup String where
  (<+>) = (++)

instance Monoid String where
  neutral = ""

span : (Char -> Bool) -> String -> (String, String)
span p xs with (strM xs)
  span p ""             | StrNil        = ("", "")
  span p (strCons x xs) | (StrCons _ _) with (p x)
    | True with (assert_total (span p xs))
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
        = if (isSpace x) then assert_total (ltrim xs) else (strCons x xs)

trim : String -> String
trim xs = ltrim (reverse (ltrim (reverse xs)))

words' : List Char -> List (List Char)
words' s = case dropWhile isSpace s of
            [] => []
            s' => let (w, s'') = break isSpace s'
                  in w :: words' (assert_smaller s s'')

words : String -> List String
words s = map pack $ words' $ unpack s

lines' : List Char -> List (List Char)
lines' s = case dropWhile isNL s of
            [] => []
            s' => let (w, s'') = break isNL s'
                  in w :: lines' (assert_smaller s s'')

lines : String -> List String
lines s = map pack $ lines' $ unpack s

partial
foldr1 : (a -> a -> a) -> List a -> a
foldr1 f [x] = x
foldr1 f (x::xs) = f x (foldr1 f xs)

unwords' : List (List Char) -> List Char
unwords' [] = []
unwords' ws = assert_total (foldr1 addSpace ws)
        where
            addSpace : List Char -> List Char -> List Char
            addSpace w s = w ++ (' ' :: s)

unwords : List String -> String
unwords = pack . unwords' . map unpack

length : String -> Nat
length = fromInteger . prim__zextInt_BigInt . prim_lenString
