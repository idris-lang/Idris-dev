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

main : UnsafeIO ()
main = do print (h True); print (h False)
