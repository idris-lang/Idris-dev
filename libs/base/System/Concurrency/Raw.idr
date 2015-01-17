-- WARNING: No guarantees that this works properly yet!

module System.Concurrency.Raw

-- Raw (i.e. not type safe) message passing

import System

||| Send a message of any type to the thread with the given thread id
sendToThread : (thread_id : Ptr) -> a -> IO ()
sendToThread {a} dest val
   = foreign FFI_C "idris_sendMessage" (Ptr -> Ptr -> Raw a -> IO ())
                prim__vm dest (MkRaw val)

checkMsgs : IO Bool
checkMsgs = do msgs <- foreign FFI_C "idris_checkMessages" (Ptr -> IO Int)
                            prim__vm
               return (intToBool msgs)

||| Check inbox for messages. If there are none, blocks until a message
||| arrives.
getMsg : IO a
getMsg {a} = do MkRaw x <- foreign FFI_C "idris_recvMessage"
                             (Ptr -> IO (Raw a)) prim__vm
                return x
