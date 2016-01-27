module Prelude.Strings

import Builtins
import IO

import Prelude.Algebra
import Prelude.Basics
import Prelude.Bool
import Prelude.Chars
import Prelude.Cast
import Prelude.Interfaces
import Prelude.Either
import Prelude.Foldable
import Prelude.Functor
import Prelude.List
import Prelude.Nat
import Prelude.Monad
import Decidable.Equality

partial
foldr1 : (a -> a -> a) -> List a -> a
foldr1 _ [x] = x
foldr1 f (x::xs) = f x (foldr1 f xs)

partial
foldl1 : (a -> a -> a) -> List a -> a
foldl1 f (x::xs) = foldl f x xs

||| Appends two strings together.
|||
||| ```idris example
||| "AB" ++ "C"
||| ```
(++) : String -> String -> String
(++) = prim__concat

||| Returns the first character in the specified string.
|||
||| Doesn't work for empty strings.
|||
||| ```idris example
||| strHead "A"
||| ```
partial
strHead : String -> Char
strHead = prim__strHead

||| Returns the characters specified after the head of the string.
|||
||| Doesn't work for empty strings.
|||
||| ```idris example
||| strTail "AB"
||| ```
||| ```idris example
||| strTail "A"
||| ```
partial
strTail : String -> String
strTail = prim__strTail

||| Adds a character to the front of the specified string.
|||
||| ```idris example
||| strCons 'A' "B"
||| ```
||| ```idris example
||| strCons 'A' ""
||| ```
strCons : Char -> String -> String
strCons = prim__strCons

||| Returns the nth character (starting from 0) of the specified string.
|||
||| Precondition: '0 < i < length s' for 'strIndex s i'.
|||
||| ```idris example
||| strIndex "AB" 1
||| ```
partial
strIndex : String -> Int -> Char
strIndex = prim__strIndex

||| Reverses the elements within a String.
|||
||| ```idris example
||| reverse "ABC"
||| ```
||| ```idris example
||| reverse ""
||| ```
reverse : String -> String
reverse = prim__strRev

null : Ptr
null = prim__null

-- Some more complex string operations

data StrM : String -> Type where
    StrNil : StrM ""
    StrCons : (x : Char) -> (xs : String) -> StrM (strCons x xs)

||| Version of 'strHead' that statically verifies that the string is not empty.
strHead' : (x : String) -> (not (x == "") = True) -> Char
strHead' x p = assert_total $ prim__strHead x

||| Version of 'strTail' that statically verifies that the string is not empty.
strTail' : (x : String) -> (not (x == "") = True) -> String
strTail' x p = assert_total $ prim__strTail x

-- we need the 'believe_me' because the operations are primitives
strM : (x : String) -> StrM x
strM x with (decEq (not (x == "")) True)
  strM x | (Yes p) = really_believe_me $
                           StrCons (assert_total (strHead' x p))
                                   (assert_total (strTail' x p))
  strM x | (No p) = really_believe_me StrNil

-- annoyingly, we need these assert_totals because StrCons doesn't have
-- a recursive argument, therefore the termination checker doesn't believe
-- the string is guaranteed smaller. It makes a good point.

||| Turns a string into a list of characters.
|||
||| ```idris example
||| unpack "ABC"
||| ```
unpack : String -> List Char
unpack s with (strM s)
  unpack ""             | StrNil = []
  unpack (strCons x xs) | (StrCons x xs) = x :: assert_total (unpack xs)

||| Turns a Foldable of characters into a string.
pack : (Foldable t) => t Char -> String
pack = foldr strCons ""

||| Creates a string of a single character.
|||
||| ```idris example
||| singleton 'A'
||| ```
singleton : Char -> String
singleton c = strCons c ""

Cast String (List Char) where
  cast = unpack

Cast (List Char) String where
  cast = pack

Cast Char String where
  cast = singleton

Semigroup String where
  (<+>) = (++)

Monoid String where
  neutral = ""

||| Splits the string into a part before the predicate
||| returns False and the rest of the string.
|||
||| ```idris example
||| span (/= 'C') "ABCD"
||| ```
||| ```idris example
||| span (/= 'C') "EFGH"
||| ```
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
||| ```idris example
||| break (== 'C') "ABCD"
||| ```
||| ```idris example
||| break (== 'C') "EFGH"
||| ```
break : (Char -> Bool) -> String -> (String, String)
break p = span (not . p)

||| Splits the string into parts with the predicate
||| indicating separator characters.
|||
||| ```idris example
||| split (== '.') ".AB.C..D"
||| ```
split : (Char -> Bool) -> String -> List String
split p xs = map pack (split p (unpack xs))

||| Removes whitespace (determined with 'isSpace') from
||| the start of the string.
|||
||| ```idris example
||| ltrim " A\nB"
||| ```
||| ```idris example
||| ltrim " \nAB"
||| ```
ltrim : String -> String
ltrim xs with (strM xs)
    ltrim "" | StrNil = ""
    ltrim (strCons x xs) | StrCons _ _
        = if (isSpace x) then assert_total (ltrim xs) else (strCons x xs)

||| Removes whitespace (determined with 'isSpace') from
||| the start and end of the string.
|||
||| ```idris example
||| trim " A\nB C "
||| ```
trim : String -> String
trim xs = ltrim (reverse (ltrim (reverse xs)))

||| Splits a character list into a list of whitespace separated character lists.
|||
||| ```idris example
||| words' (unpack " A B C  D E   ")
||| ```
words' : List Char -> List (List Char)
words' s = case dropWhile isSpace s of
            [] => []
            s' => let (w, s'') = break isSpace s'
                  in w :: words' (assert_smaller s s'')

||| Splits a string into a list of whitespace separated strings.
|||
||| ```idris example
||| words " A B C  D E   "
||| ```
words : String -> List String
words s = map pack $ words' $ unpack s

||| Splits a character list into a list of newline separated character lists.
|||
||| ```idris example
||| lines' (unpack "\rA BC\nD\r\nE\n")
||| ```
lines' : List Char -> List (List Char)
lines' s = case dropWhile isNL s of
            [] => []
            s' => let (w, s'') = break isNL s'
                  in w :: lines' (assert_smaller s s'')

||| Splits a string into a list of newline separated strings.
|||
||| ```idris example
||| lines  "\rA BC\nD\r\nE\n"
||| ```
lines : String -> List String
lines s = map pack $ lines' $ unpack s

||| Joins the character lists by spaces into a single character list.
|||
||| ```idris example
||| unwords' [['A'], ['B', 'C'], ['D'], ['E']]
||| ```
unwords' : List (List Char) -> List Char
unwords' [] = []
unwords' ws = assert_total (foldr1 addSpace ws) where
  addSpace : List Char -> List Char -> List Char
  addSpace w s = w ++ (' ' :: s)

||| Joins the strings by spaces into a single string.
|||
||| ```idris example
||| unwords ["A", "BC", "D", "E"]
||| ```
unwords : List String -> String
unwords = pack . unwords' . map unpack

||| Joins the character lists by newlines into a single character list.
|||
||| ```idris example
||| unlines' [['l','i','n','e'], ['l','i','n','e','2'], ['l','n','3'], ['D']]
||| ```
unlines' : List (List Char) -> List Char
unlines' [] = []
unlines' ls = assert_total (foldr1 addLine ls) where
  addLine : List Char -> List Char -> List Char
  addLine l s = l ++ ('\n' :: s)

||| Joins the strings by newlines into a single string.
|||
||| ```idris example
||| unlines ["line", "line2", "ln3", "D"]
||| ```
unlines : List String -> String
unlines = pack . unlines' . map unpack

||| Returns the length of the string.
|||
||| ```idris example
||| length ""
||| ```
||| ```idris example
||| length "ABC"
||| ```
length : String -> Nat
length = fromInteger . prim__zextInt_BigInt . prim_lenString

||| Returns a substring of a given string
|||
||| @ index The (zero based) index of the string to extract. If this is
|||         beyond the end of the string, the function returns the empty
|||         string.
||| @ len The desired length of the substring. Truncated if this exceeds
|||       the length of the input.
||| @ subject The string to return a portion of
substr : (index : Nat) -> (len : Nat) -> (subject : String) -> String
substr i len subject = prim__strSubstr (cast i) (cast len) subject

||| Lowercases all characters in the string.
|||
||| ```idris example
||| toLower "aBc12!"
||| ```
toLower : String -> String
toLower x with (strM x)
  strToLower ""             | StrNil = ""
  strToLower (strCons c cs) | (StrCons c cs) =
    strCons (toLower c) (toLower (assert_smaller (strCons c cs) cs))

||| Uppercases all characters in the string.
|||
||| ```idris example
||| toLower "aBc12!"
||| ```
toUpper : String -> String
toUpper x with (strM x)
  strToLower ""             | StrNil = ""
  strToLower (strCons c cs) | (StrCons c cs) =
    strCons (toUpper c) (toUpper (assert_smaller (strCons c cs) cs ))

--------------------------------------------------------------------------------
-- Predicates
--------------------------------------------------------------------------------

isPrefixOf : String -> String -> Bool
isPrefixOf a b = isPrefixOf (unpack a) (unpack b)

isSuffixOf : String -> String -> Bool
isSuffixOf a b = isSuffixOf (unpack a) (unpack b)

isInfixOf : String -> String -> Bool
isInfixOf a b = isInfixOf (unpack a) (unpack b)

||| Check if a foreign pointer is null
partial
nullPtr : Ptr -> IO Bool
nullPtr p = do ok <- foreign FFI_C "isNull" (Ptr -> IO Int) p
               return (ok /= 0)

||| Check if a supposed string was actually a null pointer
partial
nullStr : String -> IO Bool
nullStr p = do ok <- foreign FFI_C "isNull" (String -> IO Int) p
               return (ok /= 0)
