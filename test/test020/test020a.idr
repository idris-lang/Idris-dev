module Main

implicit 
forget : Vect n a -> List a
forget [] = []
forget (x :: xs) = x :: forget xs

implicit
forget' : Vect n a -> List a
forget' [] = []
forget' (x :: xs) = forget xs

foo : Vect n a -> List a
foo xs = reverse xs

main : UnsafeIO ()
main = print (foo [1,2,3])

