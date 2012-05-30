module main

forLoop : List a -> (a -> IO ()) -> IO ()
forLoop [] f = return ()
forLoop (x :: xs) f = do f x
                         forLoop xs f

syntax for {x} "in" [xs] [body] = forLoop xs (\x => body)

main : IO ()
main = do putStrLn "Counting:"
          for x in [1..10] do
              putStrLn $ "Number " ++ show x
          putStrLn "Done!"

