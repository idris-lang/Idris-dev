module Main

import Text.PrettyPrint.WL

%default total

myDoc : Doc
myDoc = fold (|//|) $ map text $ words "this is a long sentence with a lot of words that I can use for testing the performance of the prettier printer implementation. I need a few more words to prove my point, though."

myString : String
myString =  toString 0 15 $ myDoc

main : IO ()
main = putStrLn myString
