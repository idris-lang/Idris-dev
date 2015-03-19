module Main

import Data.Hash

main : IO ()
main = do printLn $ hash (the Bits8 3)
          printLn $ hash (the (List Bits8) [3])
          printLn $ hash "hello world"
          printLn $ hash 'a'
          printLn $ hash (the Bits8 3)
          printLn $ hash (the Bits16 3)
          printLn $ hash (the Bits32 3)
          printLn $ hash (the Bits64 3)
          printLn $ hash (the Int 3)
          printLn $ hash (the Integer 3)

