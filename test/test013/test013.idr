module Main

forLoop : List a -> (a -> UnsafeIO ()) -> UnsafeIO ()
forLoop [] f = return ()
forLoop (x :: xs) f = do f x
                         forLoop xs f

syntax for {x} "in" [xs] ":" [body] = forLoop xs (\x => body)

main : UnsafeIO ()
main = do putStrLn "Counting:"
          for x in [1..10]: 
              putStrLn $ "Number " ++ show x
          putStrLn "Done!"

