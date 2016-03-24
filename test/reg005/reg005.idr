module UPIO

foo : List (IO ())
foo = [putStrLn "hey", putStrLn "you"]

namespace Main
  main : IO ()
  main = let stuff = map unsafePerformIO foo in putStrLn (show stuff)

