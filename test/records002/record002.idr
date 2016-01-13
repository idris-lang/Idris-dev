record Foo (param : Nat) where
  constructor MkFoo
  num : Int

implementation Show (Foo n) where
  show f = show (param_param f) ++ ", " ++ show (num f)

main : IO ()
main = do let x = MkFoo {param=10} 20
          putStrLn (show (record { param_param = 42 } x))
          putStrLn (show (record { num = 42 } x))

