module Main

main : UnsafeIO ()
main = do l <- getLine
          let ll = l ++ l
          putStrLn ll