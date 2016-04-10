import Data.List.Views

rev : List a -> List a
rev xs with (snocList xs)
  rev [] | Empty = []
  rev (ys ++ [x]) | (Snoc y) = x :: rev ys | y

-- Show all the splits for all the recursive calls, to demonstrate they really
-- are split in half
showDivisions : (xs : List a) -> List (List a)
showDivisions xs with (splitRec xs)
  showDivisions [] | SplitRecNil = []
  showDivisions [x] | SplitRecOne = [[x]]
  showDivisions (ys ++ zs) | (SplitRecPair ysrec zsrec) = 
    (ys ++ zs) :: showDivisions ys | ysrec ++ showDivisions zs | zsrec

total
mergeSort : Ord a => List a -> List a
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
main = do let list = testList 100 12345 []
          putStrLn "Sorting list"
          let list' = mergeSort list
          printLn list'
          printLn (rev list')


