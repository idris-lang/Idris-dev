module Main

import Data.Buffer

em : Buffer 0
em = allocate 4

one : Bits32
one = 1

two : Bits8
two = 2

firstHalf : Buffer 4
firstHalf = appendBits32LE em 1 one

full : Buffer 8
full = appendBits8LE firstHalf 4 two

firstByte : Bits8
firstByte = peekBits8LE full 0

firstHalfView : Buffer 4
firstHalfView = peekBufferLE full 0

firstHalfCopy : Buffer 4
firstHalfCopy = copy firstHalfView

oneFromFirstHalf : Bits32
oneFromFirstHalf = peekBits32LE firstHalf 0

oneFromFirstHalfCopy : Bits32
oneFromFirstHalfCopy = peekBits32LE firstHalfCopy 0

viewsAndCopiesPreserveEquality : Bool
viewsAndCopiesPreserveEquality = ( oneFromFirstHalf == one ) && ( oneFromFirstHalfCopy == one )

secondHalfWord : Bits32
secondHalfWord = peekBits32LE full 1

main : IO ()
main = do
  putStrLn $ show firstByte
  putStrLn $ show viewsAndCopiesPreserveEquality
  putStrLn $ show secondHalfWord
