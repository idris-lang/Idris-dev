import Data.List.Views

total
qsort : Ord a => (xs : List a) -> List a
qsort inp with (filtered (<) inp)
  qsort [] | FNil = []
  qsort (x :: xs) | (FRec lrec rrec) 
     = qsort (filter (\v => v < x) xs) | lrec ++
         x :: qsort (filter (\v => not (v < x)) xs) | rrec

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
          let list' = qsort list
          printLn list'

