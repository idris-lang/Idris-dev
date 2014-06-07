module Prelude.Strings

import Builtins
import Prelude.List
import Prelude.Chars
import Prelude.Cast
import Prelude.Either
import Prelude.Foldable

||| Appends two strings together.
|||
||| Idris> "AB" ++ "C"
||| "ABC" : String
(++) : String -> String -> String
(++) = prim__concat

||| Returns the first character in the specified string.
|||
||| Doesn't work for empty strings.
|||
||| Idris> strHead "A"
||| 'A' : Char
partial
strHead : String -> Char
strHead = prim__strHead

||| Returns the characters specified after the head of the string.
|||
||| Doesn't work for empty strings.
|||
||| Idris> strTail "AB"
||| "B" : String
||| Idris> strTail "A"
||| "" : String
partial
strTail : String -> String
strTail = prim__strTail

||| Adds a character to the front of the specified string.
|||
||| Idris> strCons 'A' "B"
||| "AB" : String
||| Idris> strCons 'A' ""
||| "A" : String
strCons : Char -> String -> String
strCons = prim__strCons

||| Returns the nth character (starting from 0) of the specified string.
|||
||| Precondition: '0 < i < length s' for 'strIndex s i'.
|||
||| Idris> strIndex "AB" 1
||| 'B' : Char
partial
strIndex : String -> Int -> Char
strIndex = prim__strIndex

||| Reverses the elements within a String.
|||
||| Idris> reverse "ABC"
||| "CBA" : String
||| Idris> reverse ""
||| "" : String
reverse : String -> String
reverse = prim__strRev

null : Ptr
null = prim__null

-- Some more complex string operations

data StrM : String -> Type where
    StrNil : StrM ""
    StrCons : (x : Char) -> (xs : String) -> StrM (strCons x xs)

||| Version of 'strHead' that statically verifies that the string is not empty.
strHead' : (x : String) -> so (not (x == "")) -> Char
strHead' x p = assert_total $ prim__strHead x

||| Version of 'strTail' that statically verifies that the string is not empty.
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

||| Turns a string into a list of characters.
|||
||| Idris> unpack "ABC"
||| ['A', 'B', 'C'] : List Char
unpack : String -> List Char
unpack s with (strM s)
  unpack ""             | StrNil = []
  unpack (strCons x xs) | (StrCons x xs) = x :: assert_total (unpack xs)

||| Turns a Foldable of characters into a string.
pack : (Foldable t) => t Char -> String
pack = foldr strCons ""

||| Creates a string of a single character.
|||
||| Idris> singleton 'A'
||| "A" : String
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

||| Splits the string into a part before the predicate
||| returns False and the rest of the string.
|||
||| Idris> span (/= 'C') "ABCD"
||| ("AB", "CD") : (String, String)
||| Idris> span (/= 'C') "EFGH"
||| ("EFGH", "") : (String, String)
span : (Char -> Bool) -> String -> (String, String)
span p xs with (strM xs)
  span p ""             | StrNil        = ("", "")
  span p (strCons x xs) | (StrCons _ _) with (p x)
    | True with (assert_total (span p xs))
      | (ys, zs) = (strCons x ys, zs)
    | False = ("", strCons x xs)

||| Splits the string into a part before the predicate
||| returns True and the rest of the string.
|||
||| Idris> break (== 'C') "ABCD"
||| ("AB", "CD") : (String, String)
||| Idris> break (== 'C') "EFGH"
||| ("EFGH", "") : (String, String)
break : (Char -> Bool) -> String -> (String, String)
break p = span (not . p)

||| Splits the string into parts with the predicate
||| indicating separator characters.
|||
||| Idris> split (== '.') ".AB.C..D"
||| ["", "AB", "C", "", "D"] : List String
split : (Char -> Bool) -> String -> List String
split p xs = map pack (split p (unpack xs))

||| Removes whitespace (determined with 'isSpace') from
||| the start of the string.
|||
||| Idris> ltrim " A\nB"
||| "A\nB" : String
||| Idris> ltrim " \nAB"
||| "AB" : String
ltrim : String -> String
ltrim xs with (strM xs)
    ltrim "" | StrNil = ""
    ltrim (strCons x xs) | StrCons _ _
        = if (isSpace x) then assert_total (ltrim xs) else (strCons x xs)

||| Removes whitespace (determined with 'isSpace') from
||| the start and end of the string.
|||
||| Idris> trim " A\nB C "
||| "A\nB C" : String
trim : String -> String
trim xs = ltrim (reverse (ltrim (reverse xs)))

||| Splits a character list into a list of whitespace separated character lists.
|||
||| Idris> words' (unpack " A B C  D E   ")
||| [['A'], ['B'], ['C'], ['D'], ['E']] : List (List Char)
words' : List Char -> List (List Char)
words' s = case dropWhile isSpace s of
            [] => []
            s' => let (w, s'') = break isSpace s'
                  in w :: words' (assert_smaller s s'')

||| Splits a string into a list of whitespace separated strings.
|||
||| Idris> words " A B C  D E   "
||| ["A", "B", "C", "D", "E"] : List String
words : String -> List String
words s = map pack $ words' $ unpack s

||| Splits a character list into a list of newline separated character lists.
|||
||| Idris> lines' (unpack "\rA BC\nD\r\nE\n")
||| [['A', ' ', 'B', 'C'], ['D'], ['E']] : List (List Char)
lines' : List Char -> List (List Char)
lines' s = case dropWhile isNL s of
            [] => []
            s' => let (w, s'') = break isNL s'
                  in w :: lines' (assert_smaller s s'')

||| Splits a string into a list of newline separated strings.
|||
||| Idris> lines  "\rA BC\nD\r\nE\n"
||| ["A BC", "D", "E"] : List String
lines : String -> List String
lines s = map pack $ lines' $ unpack s

partial
foldr1 : (a -> a -> a) -> List a -> a
foldr1 _ [x] = x
foldr1 f (x::xs) = f x (foldr1 f xs)

partial
foldl1 : (a -> a -> a) -> List a -> a
foldl1 f (x::xs) = foldl f x xs

||| Joins the character lists by spaces into a single character list.
|||
||| Idris> unwords' [['A'], ['B', 'C'], ['D'], ['E']]
||| ['A', ' ', 'B', 'C', ' ', 'D', ' ', 'E'] : List Char
unwords' : List (List Char) -> List Char
unwords' [] = []
unwords' ws = assert_total (foldr1 addSpace ws)
        where
            addSpace : List Char -> List Char -> List Char
            addSpace w s = w ++ (' ' :: s)

||| Joins the strings by spaces into a single string. 
|||
||| Idris> unwords ["A", "BC", "D", "E"]
||| "A BC D E" : String
unwords : List String -> String
unwords = pack . unwords' . map unpack

||| Returns the length of the string.
|||
||| Idris> length ""
||| 0 : Nat
||| Idris> length "ABC"
||| 3 : Nat
length : String -> Nat
length = fromInteger . prim__zextInt_BigInt . prim_lenString

||| Lowercases all characters in the string.
|||
||| Idris> toLower "aBc12!"
||| "abc12!" : String
toLower : String -> String
toLower x with (strM x)
  strToLower ""             | StrNil = ""
  strToLower (strCons c cs) | (StrCons c cs) =
    strCons (toLower c) (toLower (assert_smaller (strCons c cs) cs))

||| Uppercases all characters in the string.
|||
||| Idris> toLower "aBc12!"
||| "ABC12!" : String
toUpper : String -> String
toUpper x with (strM x)
  strToLower ""             | StrNil = ""
  strToLower (strCons c cs) | (StrCons c cs) =
    strCons (toUpper c) (toUpper (assert_smaller (strCons c cs) cs ))

