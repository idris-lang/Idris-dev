module Main

import Data.Vect
import Data.Fin

total
pull : Fin (S n) -> Vect (S n) a -> (a, Vect n a)
pull {n=Z}   _      (x :: xs) = (x, xs)
-- pull {n=S q} FZ     (Vect.(::) {n=S _} x xs) = (x, xs)
pull {n=S _} (FS n) (x :: xs) =
  let (v, vs) = pull n xs in
        (v, x::vs)

main : IO ()
main = printLn (pull FZ [0, 1, 2])
