preInc : Nat -> Nat
preInc = (1 `plus`)

main : IO ()
main = do
  putStrLn $ show $ (1 `plus`) 42
  putStrLn $ show $ (1 +) 79
