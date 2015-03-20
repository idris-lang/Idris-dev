module Main

import Effects
import Effect.Select
import Effect.Exception

triple : Int -> { [SELECT, EXCEPTION String] } Eff (Int, Int, Int)
triple max = do z <- select [1..max]
                y <- select [1..z]
                x <- select [1..y]
                if (x * x + y * y == z * z)
                   then pure (x, y, z)
                   else raise "No triple"

main : IO ()
main = do print $ the (Maybe _) $ run (triple 100)
          print $ the (List _) $ run (triple 100)
