module main;

dumpFile : String -> IO ();
dumpFile fn = do { h <- openFile fn Read;
                   while (do { x <- feof h;
                               return (not x); })
                         (do { l <- fread h;
                               putStr l; });
                   closeFile h; };

main : IO ();
main = do { h <- fopen "testfile" "w";
            fwrite h "Hello!\nWorld!\n";
            fclose h;
            putStrLn "Reading testfile";
            f <- readFile "testfile";
            putStrLn f;
            putStrLn "---";
            dumpFile "testfile";
          };

