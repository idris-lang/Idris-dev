module main;

while : |(test : IO Bool) -> |(body : IO ()) -> IO ();
while t b = do { v <- t;
                 if v then (do { b; while t b; }) else return (); };


readFile : String -> IO String;
readFile fn = do { h <- fopen fn "r";
                   c <- readFile' h "";
                   fclose h;
                   return c;
                 }
  where {
    readFile' : File -> String -> IO String;
    readFile' h contents = 
       do { x <- feof h;
            if (not x) then (do { l <- fread h;
                                  readFile' h (contents ++ l);
                                })
                       else (return contents); };
  }

dumpFile : String -> IO ();
dumpFile fn = do { h <- fopen fn "r";
                   while (do { x <- feof h;
                               return (not x); })
                         (do { l <- fread h;
                               putStr l; });
                   fclose h; };

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

