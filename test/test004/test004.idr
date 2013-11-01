module Main

mwhile : |(test : IO Bool) -> |(body : IO ()) -> IO ()
mwhile t b = do v <- t
                case v of
                     True => do b
                                mwhile t b
                     False => return ()

dumpFile : String -> IO ()
dumpFile fn = do { h <- openFile fn Read
                   mwhile (do { -- putStrLn "TEST"
                                x <- feof h
                                return (not x) })
                          (do { l <- fread h
                                putStr l })
                   closeFile h }

main : IO ()
main = do { h <- openFile "testfile" Write
            fwrite h "Hello!\nWorld!\n...\n3\n4\nLast line\n"
            closeFile h
            putStrLn "Reading testfile"
            f <- readFile "testfile"
            putStrLn f
            putStrLn "---"
            dumpFile "testfile"
            putStrLn "---"
          }

