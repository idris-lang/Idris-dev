module Main

main : IO ()
main = do
  printLn $ prim_lenString "hallo"
  printLn $ prim_lenString "1"
  printLn $ prim_lenString ""

