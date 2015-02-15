-- WARNING: No guarantees that this works properly yet!

module System.Concurrency.Raw

-- Raw (i.e. not type safe) message passing

import System

||| Send a message of any type to the thread with the given thread id
sendToThread : (thread_id : Ptr) -> a -> IO ()
sendToThread {a} dest val
   = foreign FFI_C "idris_sendMessage" (Ptr -> Ptr -> Raw a -> IO ())
                prim__vm dest (MkRaw val)

||| Check for messages in the process inbox
checkMsgs : IO Bool
checkMsgs = do msgs <- foreign FFI_C "idris_checkMessages" (Ptr -> IO Int)
                            prim__vm
               return (intToBool msgs)

||| Check for messages from a specific sender in the process inbox
checkMsgsFrom : Ptr -> IO Bool
checkMsgsFrom sender
  = do msgs <- foreign FFI_C "idris_checkMessagesFrom" (Ptr -> Ptr -> IO Int)
                             prim__vm sender
       return (intToBool msgs)

||| Check inbox for messages. If there are none, blocks until a message
||| arrives.
||| Note that this is not at all type safe! It is intended to be used in
||| a type safe wrapper.
getMsg : IO a
getMsg {a} = do m <- foreign FFI_C "idris_recvMessage" 
                             (Ptr -> IO Ptr) prim__vm
                MkRaw x <- foreign FFI_C "idris_getMsg" (Ptr -> IO (Raw a)) m
                return x

||| Check inbox for messages. If there are none, blocks until a message
||| arrives. Return pair of sender's ID and the message.
||| Note that this is not at all type safe! It is intended to be used in
||| a type safe wrapper.
getMsgWithSender : IO (Ptr, a)
getMsgWithSender {a} 
           = do m <- foreign FFI_C "idris_recvMessage" 
                             (Ptr -> IO Ptr) prim__vm
                MkRaw x <- foreign FFI_C "idris_getMsg" (Ptr -> IO (Raw a)) m
                vm <- foreign FFI_C "idris_getSender" (Ptr -> IO Ptr) m
                foreign FFI_C "idris_freeMsg" (Ptr -> IO ()) m
                return (vm, x)

getMsgFrom : Ptr -> IO a
getMsgFrom {a} sender 
  = do m <- foreign FFI_C "idris_recvMessageFrom"
                    (Ptr -> Ptr -> IO Ptr) prim__vm sender
       MkRaw x <- foreign FFI_C "idris_getMsg" (Ptr -> IO (Raw a)) m
       foreign FFI_C "idris_freeMsg" (Ptr -> IO ()) m
       return x

