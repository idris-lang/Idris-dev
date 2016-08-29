import Data.List

addLists : List Int -> List Int -> List Int
addLists xs ys = xs ++ ys

nil : List Int
nil = []

cons : Int -> List Int -> List Int
cons x xs = x :: xs

show' : List Int -> IO String
show' xs = do putStrLn "Ready to show..."
              pure (show xs)

testList : FFI_Export FFI_C "testHdr.h" []
testList = Data (List Int) "ListInt" $
           Data (List Nat) "ListNat" $
           Fun addLists "addLists" $
           Fun nil "nil" $
           Fun cons "cons" $
           Data Nat "Nat" $
           Fun Strings.length "lengthS" $
           Fun show' "showList" $
           End

-- main : IO ()
-- main = do s <- show' 42
--           putStrLn s 

