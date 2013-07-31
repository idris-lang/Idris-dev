module Main

main : UnsafeIO ()
main = do
  print $ prim_lenString "hallo"
  print $ prim_lenString "1"
  print $ prim_lenString ""

