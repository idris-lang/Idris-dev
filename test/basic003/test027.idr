module Main

using (Ord a, Num n)

  isort : List a -> List a
  isort [] = []
  isort (x :: xs) = insert x (isort xs)
    where -- insert : a -> List a -> List a
          insert x [] = [x]
          insert x (y :: ys) = if x < y then x :: y :: ys
                                         else y :: insert x ys

  msum : Num n => List n -> n
  msum [] = 0
  msum (x :: xs) = x + msum xs

  mprod : List n -> n
  mprod [] = 1
  mprod (x :: xs) = x * mprod xs

main : IO ()
main = do printLn $ isort [1,5,3,5,1,9,8]
          printLn $ msum [1..10]
          printLn $ mprod [1..10]

