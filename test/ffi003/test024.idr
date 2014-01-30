module Main

main : IO ()
main = do l <- getLine
          let ll = l ++ l
          putStrLn ll
