preInc : Nat -> Nat
preInc = (1 `plus`)

postInc : Nat -> Nat
postInc = (`plus` 1)

main : IO ()
main = do
  printLn $ (1 `plus`) 42 == 43
  printLn $ (1 +) 2 == 3
  printLn $ (`plus` 1) 67 == 68
  printLn $ (+ 1) 77 == 78
  let x : Integer = 4
  printLn $ (- x) == -4         -- prefix, not section
  let io : IO Integer = pure 9
  printLn $ (! io) == 9         -- prefix, not section
