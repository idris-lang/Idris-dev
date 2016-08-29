module Main

mwhile : (test : IO Bool) -> (body : IO ()) -> IO ()
mwhile t b = do v <- t
                case v of
                     True => do b
                                mwhile t b
                     False => pure ()

dumpFile : String -> IO ()
dumpFile fn = do { Right h <- openFile fn Read
                   mwhile (do { -- putStrLn "TEST"
                                x <- fEOF h
                                pure (not x) })
                          (do { Right l <- fGetLine h
                                putStr l })
                   closeFile h }

main : IO ()
main = do { Right h <- openFile "testfile" WriteTruncate
            fPutStr h "Hello!\nWorld!\n...\n3\n4\nLast line\n"
            closeFile h
            putStrLn "Reading testfile"
            Right f <- readFile "testfile"
            putStrLn f
            putStrLn "---"
            dumpFile "testfile"
            putStrLn "---"
          }

