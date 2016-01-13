module Main

corecord Str a where -- Current stream is codata, not a corecord
  constructor (::)
  head : a
  tail : Str a

implementation Functor Str where
  map f (x :: xs) = (f x) :: (map f xs)

total -- marked total to check that corecords are indeed treated as coinductive types
zeros : Str Int
zeros = 0 :: zeros

ones : Str Int
ones = map (1+) zeros

main : IO ()
main = do let x = record { head = 1 } zeros
          printLn $ head zeros
          printLn $ head x
          printLn $ head (record { head = 3 } x)
          printLn $ head (tail ones)
          printLn $ head (tail (record { tail = zeros } ones))
