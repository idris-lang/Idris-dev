module Main

import System
import System.Concurrency.Raw

recvMsg : IO (Ptr, String)
recvMsg = getMsg

pong : IO ()
pong = do -- putStrLn "Waiting for ping"
          (sender, x) <- recvMsg
          putStrLn x
          putStrLn "Received"
          sendToThread sender "Hello to you too!"

ping : Ptr -> IO ()
ping thread = sendToThread thread (prim__vm, "Hello!")

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

