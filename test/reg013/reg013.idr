module Main

main : IO ()
main = do
  print $ prim_lenString "hallo"
  print $ prim_lenString "1"
  print $ prim_lenString ""

