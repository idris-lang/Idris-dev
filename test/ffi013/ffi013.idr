module Main

main : IO ()
main = do b <- fRemove "remove.me"
          putStrLn $ if b then "success" else "failure"