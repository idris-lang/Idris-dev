-- | Functions operating over Char's
module Prelude.Char

import Builtins

-- | Return the ASCII representation of the character.
chr : Int -> Char
chr x = prim__intToChar x

-- | Convert the number to its ASCII equivalent.
ord : Char -> Int
ord x = prim__charToInt

-- | Returns true if the character is in the range [A-Z].
isUpper : Char -> Bool
isUpper x = x >= 'A' && x <= 'Z'

-- | Returns true if the character is in the range [a-z]
isLower : Char -> Bool
isLower x = x >= 'a' && x <= 'z'

-- | Returns true if the character is in the ranges [A-Z][a-z].
isAlpha : Char -> Bool
isAlpha x = isUpper x || isLower x

-- | Returns true if the character is in the range [0-9]
isDigit : Char -> Bool
isDigit x = (x >= '0' && x <= '9')

-- | Returns true if the character is in the ranges [A-Z][a-z][0-9]
isAlphaNum : Char -> Bool
isAlphaNum x = isDigit x || isAlpha x

-- | Returns true if the character is a whitespace character.
isSpace : Char -> Bool
isSpace x = x == ' '  || x == '\t' || x == '\r' ||
            x == '\n' || x == '\f' || x == '\v' ||
            x == '\xa0'

-- | Returns true if the character represents a new line.
isNL : Char -> Bool
isNL x = x == '\r' || x == '\n'

-- | Convert a letter to the corresponding upper-case letter, if any.
-- Non-letters are ignored.
toUpper : Char -> Char
toUpper x = if (isLower x)
               then (prim__intToChar (prim__charToInt x - 32))
               else x

-- | Convert a letter to the corresponding lower-case letter, if any.
-- Non-letters are ignored.
toLower : Char -> Char
toLower x = if (isUpper x)
               then (prim__intToChar (prim__charToInt x + 32))
               else x

-- | Returns true if the character is a hexadecimal digit i.e. in the range [0-9][a-f][A-F]
isHexDigit : Char -> Bool
isHexDigit x = elem (toUpper x) hexChars where
  hexChars : List Char
  hexChars = ['0', '1', '2', '3', '4', '5', '6', '7', '8', '9',
              'A', 'B', 'C', 'D', 'E', 'F']

-- | Returns true if the character is an octal digit.
isOctDigit : Char -> Bool
isOctDigit x = (x >= '0' && x <= '9')

-- --------------------------------------------------------------------- [ EOF ]
