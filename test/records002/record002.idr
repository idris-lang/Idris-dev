
record Foo : Nat -> Type where
       MkFoo : (param : Nat) -> (num : Int) -> Foo param

instance Show (Foo n) where
  show f = show (param f) ++ ", " ++ show (num f)

main : IO ()
main = do let x = MkFoo 10 20
          putStrLn (show (record { param = 42 } x))
          putStrLn (show (record { num = 42 } x))
