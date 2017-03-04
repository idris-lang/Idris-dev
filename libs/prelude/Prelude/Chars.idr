||| Functions operating over Chars.
|||
||| The representation of a Char is backend dependent,
||| for the C backend, it is a Unicode code point.
|||
module Prelude.Chars
-- Functions operating over Chars

import Prelude.Bool
import Prelude.Interfaces
import Prelude.List
import Prelude.Cast
import Builtins

%access public export

||| Convert the number to its backend dependent (usually Unicode) Char equivelent.
chr : Int -> Char
chr x = if (x >= 0 && x < 0x110000)
                then assert_total (prim__intToChar x)
                else '\0'

Cast Int Char where
    cast = chr

||| Return the backend dependent (usually Unicode) numerical equivelent of the Char.
ord : Char -> Int
ord x = prim__charToInt x

||| Returns true if the character is in the range [A-Z].
isUpper : Char -> Bool
isUpper x = x >= 'A' && x <= 'Z'

||| Returns true if the character is in the range [a-z]
isLower : Char -> Bool
isLower x = x >= 'a' && x <= 'z'

||| Returns true if the character is in the ranges [A-Z][a-z].
isAlpha : Char -> Bool
isAlpha x = isUpper x || isLower x

||| Returns true if the character is in the range [0-9]
isDigit : Char -> Bool
isDigit x = (x >= '0' && x <= '9')

||| Returns true if the character is in the ranges [A-Z][a-z][0-9]
isAlphaNum : Char -> Bool
isAlphaNum x = isDigit x || isAlpha x

||| Returns true if the character is a whitespace character.
isSpace : Char -> Bool
isSpace x = x == ' '  || x == '\t' || x == '\r' ||
            x == '\n' || x == '\f' || x == '\v' ||
            x == '\xa0'

||| Returns true if the character represents a new line.
isNL : Char -> Bool
isNL x = x == '\r' || x == '\n'

||| Convert a letter to the corresponding upper-case letter, if any.
||| Non-letters are ignored.
toUpper : Char -> Char
toUpper x = if (isLower x)
               then assert_total (prim__intToChar (prim__charToInt x - 32))
               else x

||| Convert a letter to the corresponding lower-case letter, if any.
||| Non-letters are ignored.
toLower : Char -> Char
toLower x = if (isUpper x)
               then assert_total (prim__intToChar (prim__charToInt x + 32))
               else x

||| Returns true if the character is a hexadecimal digit i.e. in the range [0-9][a-f][A-F]
isHexDigit : Char -> Bool
isHexDigit x = elem (toUpper x) hexChars where
  hexChars : List Char
  hexChars = ['0', '1', '2', '3', '4', '5', '6', '7', '8', '9',
              'A', 'B', 'C', 'D', 'E', 'F']

||| Returns true if the character is an octal digit.
isOctDigit : Char -> Bool
isOctDigit x = (x >= '0' && x <= '7')
