module Main

instance Show (Int -> b) where
    show x = "<<int fn>>"

instance Show (Char -> b) where
    show x = "<<char fn>>"

IntFn : Type -> Type
IntFn = \x => Int -> x

instance Functor IntFn where -- (\x => Int -> x) where
  map f intf = \x => f (intf x)

instance Apply (\x => Int -> x) where
  (<$>) f a = \x => f x (a x)

instance Applicative (\x => Int -> x) where
  pure v = \x => v

instance Bind IntFn where 
  f >>= k = \x => k (f x) x

instance Monad IntFn where

dbl : IntFn Int
dbl x = x * 2 

foo : Int -> String
foo = do val <- dbl
         \x => show val

main : IO ()
main = do print dbl
          putStrLn (foo 3)

