module Main

import System
import System.Concurrency.Raw

recvMsg : UnsafeIO (Ptr, String)
recvMsg = getMsg

pong : UnsafeIO ()
pong = do -- putStrLn "Waiting for ping"
          (sender, x) <- recvMsg
          putStrLn x
          putStrLn "Received"
          sendToThread sender "Hello to you too!"

ping : Ptr -> UnsafeIO ()
ping thread = sendToThread thread (prim__vm, "Hello!")

pingpong : UnsafeIO ()
pingpong 
     = do th <- fork pong
          putStrLn "Sending"
          ping th 
          reply <- getMsg
          putStrLn reply
          usleep 100000
          putStrLn "Finished"

main : UnsafeIO ()
main = do pingpong; pingpong; pingpong

