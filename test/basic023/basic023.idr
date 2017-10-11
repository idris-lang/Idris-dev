preInc : Nat -> Nat
preInc = (1 `plus`)

main : IO ()
main = putStrLn $ show $ preInc 42
