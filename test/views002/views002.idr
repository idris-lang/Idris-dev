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
testList x seed acc = testList (x - 1) (seed * 12345 + 789) 
                               ((seed `mod` 100) :: acc)

myhead : List a -> a
myhead (x :: xs) = x

main : IO ()
main = do let list = testList 100 12345 []
          putStrLn "Sorting list"
          let list' = qsort list
          printLn list'

