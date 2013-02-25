module Main

implicit 
forget : Vect a n -> List a
forget [] = []
forget (x :: xs) = x :: forget xs

implicit
forget' : Vect a n -> List a
forget' [] = []
forget' (x :: xs) = forget xs

foo : Vect a n -> List a
foo xs = reverse xs

main : IO ()
main = print (foo [1,2,3])


