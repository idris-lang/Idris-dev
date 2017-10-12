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
