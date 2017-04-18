module Main

echo : String -> IO ()
echo name = do Right contents <- readFile name
                   | Left error => printLn error
               printLn contents
