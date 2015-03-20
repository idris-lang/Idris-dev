module docs003

instance [mine] Functor List where
  map m [] = []
  map m (x :: xs) = m x :: map m xs

||| More functors!
instance [another] Functor List where
  map f xs = map @{mine} f xs
