import Data.Buffer

main : IO ()
main = do Just buf <- newBuffer 40
          printLn (size buf)
          setInt buf 5 (-1024567890)
          setInt buf 36 1034567890
          setString buf 20 "Hello world!"

          printLn !(bufferData buf)
          
          setDouble buf 10 123.456

          val <- getInt buf 5
          printLn val
          val <- getInt buf 6
          printLn val

          val <- getDouble buf 10
          printLn val

          val <- getInt buf 36
          printLn val
          val <- getInt buf 37 -- out of bounds, expect 0
          printLn val

          str <- getString buf 20 10
          putStrLn str
          str <- getString buf 20 12
          putStrLn str
          str <- getString buf 200 12 -- out of bounds, expect ""
          printLn str
          str <- getString buf 35 12 -- out of bounds, expect ""
          printLn str
