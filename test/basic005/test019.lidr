> module Main

> import Data.So

> ifTrue        :   So True -> Nat
> ifTrue Oh     =   S Z

> ifFalse       :   So False -> Nat
> ifFalse Oh impossible

> test          :   (f : Nat -> Bool) -> (n : Nat) -> So (f n) -> Nat
> test f n x   with   (f n)
>               |   True     =  ifTrue  x
>               |   False    =  ifFalse x

> main : IO ()
> main = printLn (test ((S 4) ==) 5 Oh)

