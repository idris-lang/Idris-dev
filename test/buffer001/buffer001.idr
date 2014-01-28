module Main

em : Buffer 0
em = allocate 32

one : Bits32
one = 1

two : Bits8
two = 2

firstHalf : Buffer 32
firstHalf = appendLE em 1 one

full : Buffer 64
full = appendLE firstHalf 4 two

firstByte : Bits8
firstByte = peekLE full 0

firstHalfView : Buffer 32
firstHalfView = peekLE full 0

firstHalfCopy : Buffer 32
firstHalfCopy = copy firstHalfView

oneFromFirstHalf : Bits32
oneFromFirstHalf = peekLE firstHalf 0

oneFromFirstHalfCopy = peekLE firstHalfCopy 0

viewsAndCopiesPreserveEquality : Bool
viewsAndCopiesPreserveEquality = (oneFromFirstHalf == one) && (oneFromFirstHalfCopy == one)

secondHalfWord : Bits32
secondHalfWord = peekLE full 1

main : IO ()
main = do
  putStrLn $ show firstByte
  putStrLn $ show viewsAndCopiesPreserveEquality
  putStrLn $ show secondHalfWord
