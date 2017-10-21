postInc : Nat -> Nat
postInc = (`plus` 1)

cons : Int -> List Int -> List Int
cons = (::)

prefix 1 :/
(:/) : Nat -> Nat
(:/) = (1 `plus`)

main : IO ()
main = do
  printLn $ (1 `cons`) [2] == [1,2]
  printLn $ (1 ::) [2]     == [1,2]
  printLn $ (`cons` [2]) 1 == [1,2]
  printLn $ (:: [2]) 1     == [1,2]
  let x : Integer = 4
  printLn $ (- x) == -4         -- prefix, not section
  let io : IO Integer = pure 9
  printLn $ (! io) == 9         -- prefix, not section
  printLn $ (:/ 3) == 4         -- custom prefix operator (#2571)
