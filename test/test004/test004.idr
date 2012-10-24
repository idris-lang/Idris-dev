module Main

dumpFile : String -> IO ()
dumpFile fn = do { h <- openFile fn Read
                   while (do { x <- feof h
                               return (not x) })
                         (do { l <- fread h
                               putStr l })
                   closeFile h }

main : IO ()
main = do { h <- openFile "testfile" Write
            fwrite h "Hello!\nWorld!\n"
            closeFile h
            putStrLn "Reading testfile"
            f <- readFile "testfile"
            putStrLn f
            putStrLn "---"
            dumpFile "testfile"
          }

