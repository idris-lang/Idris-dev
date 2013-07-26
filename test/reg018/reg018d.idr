module Main

total
pull : Fin (S n) -> Vect a (S n) -> (a, Vect a n)
pull {n=Z}   _      (x :: xs) = (x, xs)
-- pull {n=S q} fZ     (Vect.(::) {n=S _} x xs) = (x, xs)
pull {n=S _} (fS n) (x :: xs) =
  let (v, vs) = pull n xs in
        (v, x::vs)

main : IO ()
main = print (pull fZ [0, 1, 2])
