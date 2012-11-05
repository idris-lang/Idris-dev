module Main

h : Bool -> Nat
h False = r1 where
  r : Nat
  r = S O
  r1 : Nat
  r1 = r
h True = r2 where
  r : Nat
  r = O
  r2 : Nat
  r2 = r

main : IO ()
main = do print (h True); print (h False)
