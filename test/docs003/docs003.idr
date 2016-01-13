module docs003

implementation [mine] Functor List where
  map m [] = []
  map m (x :: xs) = m x :: map m xs

||| More functors!
implementation [another] Functor List where
  map f xs = map @{mine} f xs
