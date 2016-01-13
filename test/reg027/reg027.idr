module Main

implementation Show (Int -> b) where
    show x = "<<int fn>>"

implementation Show (Char -> b) where
    show x = "<<char fn>>"

IntFn : Type -> Type
IntFn = \x => Int -> x

implementation Functor IntFn where -- (\x => Int -> x) where
  map f intf = \x => f (intf x)

implementation Applicative (\x => Int -> x) where
  pure v = \x => v
  (<*>) f a = \x => f x (a x)

implementation Monad IntFn where 
  f >>= k = \x => k (f x) x

dbl : IntFn Int
dbl x = x * 2 

foo : Int -> String
foo = do val <- dbl
         \x => show val

main : IO ()
main = do printLn dbl
          putStrLn (foo 3)

