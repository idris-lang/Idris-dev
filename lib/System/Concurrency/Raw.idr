-- WARNING: No guarantees that this works properly yet! 

module System.Concurrency.Raw

-- Raw (i.e. not type safe) message passing

import System

-- Send a message of any type to the thread with the given thread id

sendToThread : (thread_id : Ptr) -> a -> IO ()
sendToThread {a} dest val 
   = mkForeign (FFun "idris_sendMessage" 
        [FPtr, FPtr, FAny a] FUnit) prim__vm dest val

checkMsgs : IO Bool
checkMsgs = do msgs <- mkForeign (FFun "idris_checkMessage"
                        [FPtr] (FInt ITNative)) prim__vm
               return (intToBool msgs)

-- Check inbox for messages. If there are none, blocks until a message
-- arrives.

getMsg : IO a
getMsg {a} = mkForeign (FFun "idris_recvMessage" 
                [FPtr] (FAny a)) prim__vm

