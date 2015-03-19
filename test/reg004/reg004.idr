module Main

h : Bool -> Nat
h False = r1 where
  r : Nat
  r = S Z
  r1 : Nat
  r1 = r
h True = r2 where
  r : Nat
  r = Z
  r2 : Nat
  r2 = r

main : IO ()
main = do printLn (h True); printLn (h False)
