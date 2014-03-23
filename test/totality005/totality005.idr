
zipWithS : (f : a -> b -> c) -> Stream a -> Stream b -> Stream c
zipWithS f (x :: xs) (y :: ys) = f x y :: zipWithS f xs ys

fib : Stream Nat
fib = 0 :: zipWithS (+) fib (1 :: fib)

main : IO ()
main = print (take 15 fib)
