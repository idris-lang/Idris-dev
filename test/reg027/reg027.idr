module Main

implementation Show (Int -> b) where
    show x = "<<int fn>>"

implementation Show (Char -> b) where
    show x = "<<char fn>>"

IntFn : Type -> Type
IntFn = \x => Int -> x

dbl : IntFn Int
dbl x = x * 2 

main : IO ()
main = printLn dbl

