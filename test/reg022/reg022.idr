module Main

millionList : List Integer
millionList = [1..1000000]

main : IO ()
main = print $ foldr (+) (the Integer 0) millionList


