import Data.Vect
import Data.Vect.Views

total
mergeSort : Ord a => Vect n a -> Vect n a
mergeSort xs with (splitRec xs)
  mergeSort [] | SplitRecNil = []
  mergeSort [x] | SplitRecOne = [x]
  mergeSort (ys ++ zs) | SplitRecPair ysrec zsrec 
      = merge (mergeSort ys | ysrec)
              (mergeSort zs | zsrec)

testList : Int -> Int -> List Int -> List Int
testList 0 seed acc = acc
-- Need to explicitly mod since different back ends overflow differently
testList x seed acc = let seed' = seed * 12345 + 768 `mod` 65536 in
                          testList (x - 1) seed' 
                               ((seed' `mod` 100) :: acc)

myhead : List a -> a
myhead (x :: xs) = x

main : IO ()
main = do let list = fromList (testList 100 12345 [])
          putStrLn "Sorting list"
          let list' = mergeSort list
          printLn list'


