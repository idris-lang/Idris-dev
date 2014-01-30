module Main

main : IO ()
main = nullPtr null >>= (putStrLn . show)
