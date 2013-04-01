module Main

main : IO ()
main = do print $ the Integer 4294967295
          print $ the Integer 4294967296
          print $ the Integer 4294967297
          print $ the Int 4294967295
          print $ the Int 4294967296
          print $ the Int 4294967297


