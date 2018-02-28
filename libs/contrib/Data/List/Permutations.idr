module Permutations

%access export

-- | All permutations of a list.
permutations : List a -> List (List a)
permutations [] = [[]]
permutations xs = [y :: zs | (y, ys) <- select xs, zs <- permutations ys]
  where
    select : List a -> List (a, List a)
    select []        = []
    select (x :: xs) = (x, xs) :: [(y, x::ys) | (y,ys) <- select xs]
