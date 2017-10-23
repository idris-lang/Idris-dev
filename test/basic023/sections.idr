postInc : Nat -> Nat
postInc = (`plus` 1)

infixr 8 `cons`
cons : Int -> List Int -> List Int
cons = (::)

namespace A
  infixr 8 `nmul`
  nmul : Nat -> Nat -> Nat
  nmul = (*)

namespace B
  nmul : Nat -> Nat -> Nat
  nmul _ y = y

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
  printLn $ 1 `cons` 2 `cons` [3] == [1,2,3]
  printLn $ 2 `A.nmul` 3 `B.nmul` 5 == 10
  printLn $ 2 `B.nmul` 3 `A.nmul` 5 == 15
