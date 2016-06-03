mutual
  data Odd : Type where
       MkOdd : Even -> Odd

  data Even : Type where
       MkEven : Odd -> Even 
       EvenZ : Even

mutual
  total
  countEven : Even -> Nat
  countEven (MkEven x) = countOdd x
  countEven EvenZ = Z

  total
  countOdd : Odd -> Nat
  countOdd (MkOdd x) = S (countEven x)
  

