module smaller

total
qsort : Ord a => List a -> List a
qsort [] = []
qsort (x :: xs) = qsort (assert_smaller (x :: xs) (filter (< x) xs)) ++ 
                  (x :: qsort (filter (>= x) xs))
