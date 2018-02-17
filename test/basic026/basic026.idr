module Main

import Data.Vect

||| Verifies that `Fin.restrict` generates a valid `Fin`
||| by using it to index a `Vect`.
main : IO ()
main = do
    let xs = the (Vect 2 Char) ['a','b']
    printLn $ Vect.index (restrict 1 0) xs == 'a'
    printLn $ Vect.index (restrict 1 1) xs == 'b'
    