> module Main

> ifTrue        :   so True -> Nat
> ifTrue oh     =   S Z

> ifFalse       :   so False -> Nat
> ifFalse oh impossible

> test          :   (f : Nat -> Bool) -> (n : Nat) -> so (f n) -> Nat
> test f n x   with   (f n)
>               |   True     =  ifTrue  x
>               |   False    =  ifFalse x

> main : IO ()
> main = print (test ((S 4) ==) 5 oh)

