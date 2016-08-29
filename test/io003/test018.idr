module Main

import System
import System.Concurrency.Raw

recvMsg : IO (Ptr, String)
recvMsg = getMsg

pong : IO ()
pong = do (sender, x) <- recvMsg
          putStrLn x
          putStrLn "Received"
          sendToThread sender 0 "Hello to you too!"
          pure ()

ping : Ptr -> IO ()
ping thread = do me <- getMyVM
                 sendToThread thread 0 (me, "Hello!")
                 pure ()

pingpong : IO ()
pingpong
     = do th <- fork pong
          putStrLn "Sending"
          ping th
          reply <- getMsg
          putStrLn reply
          usleep 100000
          putStrLn "Finished"

main : IO ()
main = do pingpong; pingpong; pingpong

