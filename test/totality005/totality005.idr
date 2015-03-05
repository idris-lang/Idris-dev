
zipWithS : (f : a -> b -> c) -> Stream a -> Stream b -> Stream c
zipWithS f (x :: xs) (y :: ys) = f x y :: zipWithS f xs ys

partial
fib : Stream Nat
fib = 0 :: zipWithS (+) fib (1 :: fib)

partial main : IO ()
main = printLn (take 15 fib)
