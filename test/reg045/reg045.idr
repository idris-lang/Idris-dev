module Main

data ListZ : Type -> Type where
  (::) : a -> Lazy (ListZ a) -> ListZ a
  Nil  : ListZ a

implementation Show a => Show (ListZ a) where
  show xs = "[" ++ show' "" xs ++ "]"
      where
        show' acc Nil        = acc
        show' acc (x :: Nil) = acc ++ show x
        show' acc (x :: xs)  = show' (acc ++ show x ++ ", ") xs

foo : ListZ Nat
foo = (1 :: 2 :: 3 :: Nil)

main : IO ()
main = printLn foo

