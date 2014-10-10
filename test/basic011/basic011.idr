module Main

import Data.Hash

main : IO ()
main = do print $ hash (the Bits8 3)
          print $ hash (the (List Bits8) [3])
          print $ hash "hello world"
          print $ hash 'a'
          print $ hash (the Bits8 3)
          print $ hash (the Bits16 3)
          print $ hash (the Bits32 3)
          print $ hash (the Bits64 3)
          print $ hash (the Int 3)
          print $ hash (the Integer 3)

