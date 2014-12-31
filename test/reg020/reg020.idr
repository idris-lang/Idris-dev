module Main

import Data.Vect

emptyString : String
emptyString = ""

helloWorld : String
helloWorld = "hello world!"

spaceOnly : String
spaceOnly = " "

tabOnly : String
tabOnly =  "\t"

linebreakOnly : String
linebreakOnly = "\n"

all : Vect 5 String
all =
  [ emptyString
  , helloWorld
  , spaceOnly
  , tabOnly
  , linebreakOnly
  ]

lengthAll : Nat
lengthAll = Strings.length $ foldl (++) (head all) (tail all)

sumOfAllLengths : Nat
sumOfAllLengths = foldl (\ l, s => l + (Strings.length s)) (Strings.length $ head all) (tail all)


main : IO ()
main = do putStrLn $ "length of: '" ++ emptyString ++ "' is: " ++ (show $ length emptyString)
          putStrLn $ "length of: '" ++ helloWorld ++ "' is: " ++ (show $ length helloWorld)
          putStrLn $ "length of: '" ++ spaceOnly ++ "' is: " ++ (show $ length spaceOnly)
          putStrLn $ "length of: '" ++ tabOnly ++ "' is: " ++ (show $ length tabOnly)
          putStrLn $ "length of: '" ++ linebreakOnly ++ "' is: " ++ (show $ length linebreakOnly)
          putStrLn $ "length of all matches sum of all lengths: " ++ (show $ lengthAll == sumOfAllLengths)

