voidIO : IO ()
voidIO = do putStrLn "aa"

intIO : IO Int
intIO = do putStrLn "bb"
           pure 123

stringIO : IO String
stringIO = do putStrLn "cc"
              pure "dd"
