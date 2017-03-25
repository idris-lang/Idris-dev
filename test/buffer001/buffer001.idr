import Data.Buffer

main : IO ()
main = do Just buf <- newBuffer 40
          printLn (size buf)
          setByte buf 5 42
          setString buf 20 "Hello world!"
          printLn !(bufferData buf)
          Just buf2 <- resizeBuffer buf 50 
          putStrLn "Resized"
          printLn !(bufferData buf2)

          putStrLn "Writing to file"
          Right h <- openFile "test.buf" WriteTruncate
          writeBufferToFile h buf (size buf)
          closeFile h

          putStrLn "Reading from file twice"
          Just buf3 <- newBuffer 80

          Right h <- openFile "test.buf" Read
          buf3 <- readBufferFromFile h buf3 (size buf3)
          closeFile h
          Right h <- openFile "test.buf" Read
          readBufferFromFile h buf3 (size buf3)
          closeFile h

          printLn !(bufferData buf3)
