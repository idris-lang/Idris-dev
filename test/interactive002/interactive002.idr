import Data.Vect

foo : ?foo_arg1 -> ?foo_arg2 -> ?foo_arg3 -> ?foo_ret
foo (S a) b c = plus (a + b + c) 42
foo Z b c = plus b c

bar : Vect n a -> Vect m a -> ?bar_out
bar xs ys = xs ++ ys

myplus : ?plus_in1 -> ?plus_in2 -> ?plus_out
myplus Z y = y
myplus (S k) y = S (myplus k y)

vfun : a -> Vect n a -> Vect n a -> Vect ?what a
vfun v xs ys = v :: ys

ifoo : ?ifoo_arg1 -> IO ?ifoo_out
ifoo x = do putStrLn x
            putStrLn "World"


