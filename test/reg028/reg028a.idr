module tbad

partial
qsort : Ord a => List a -> List a
qsort [] = []
qsort (x::xs) with (partition (<x) xs)
  qsort (x::xs) | (ys, zs) = qsort ys ++ [x] ++ qsort zs

total
qsort' : Ord a => List a -> List a
qsort' [] = []
qsort' (x::xs) with (partition (<x) xs)
  qsort' (x::xs) | (ys, zs) = ?qsortLemma

---------- Proofs ----------

qsortLemma = proof
  intros
  let ys' = qsort' ys
  let zs' = qsort' zs
  let ws = ys' ++ [x] ++ zs'
  trivial



