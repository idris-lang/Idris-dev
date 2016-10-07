module System.Concurrency.Raw

-- Raw (i.e. not type safe) message passing

import System

%access export

||| Send a message of any type to the thread with the given thread id
||| Returns channel ID if the message was sent successfully, 0 otherwise
||| 
||| @channel an ID of a specific channel to send the message on. If 0,
|||          the receiver will create a new channel ID
sendToThread : (thread_id : Ptr) -> (channel : Int) -> a -> IO Int
sendToThread {a} dest channel val
   = do me <- getMyVM
        foreign FFI_C "idris_sendMessage" (Ptr -> Int -> Ptr -> Raw a -> IO Int)
                me channel dest (MkRaw val)

||| Check for messages in the process inbox
checkMsgs : IO Bool
checkMsgs = do me <- getMyVM
               msgs <- foreign FFI_C "idris_checkMessages" (Ptr -> IO Ptr) me
               null <- nullPtr msgs
               pure (not null)

||| Check for messages in the process inbox
||| If no messages, waits for the given number of seconds
checkMsgsTimeout : Int -> IO Bool
checkMsgsTimeout timeout
          = do me <- getMyVM
               msgs <- foreign FFI_C "idris_checkMessagesTimeout" 
                            (Ptr -> Int -> IO Ptr) me timeout
               null <- nullPtr msgs
               pure (not null)

private
sender : Ptr -> IO Ptr
sender msg = foreign FFI_C "idris_getSender" (Ptr -> IO Ptr) msg

private
channel_id : Ptr -> IO Int
channel_id msg = foreign FFI_C "idris_getChannel" (Ptr -> IO Int) msg

||| Check for messages initiating a conversation in the process inbox.
||| Returns either 'Nothing', if none, or 'Just (pid, channel)' as pid 
||| of sender and new channel id.
listenMsgs : IO (Maybe (Ptr, Int))
listenMsgs = do me <- getMyVM
                msg <- foreign FFI_C "idris_checkInitMessages" (Ptr -> IO Ptr)
                             me
                null <- nullPtr msg
                if null then pure Nothing
                        else do s_id <- sender msg
                                c_id <- channel_id msg
                                pure (Just (s_id, c_id))

||| Check for messages from a specific sender/channel in the process inbox
||| If channel is '0', accept on any channel.
checkMsgsFrom : Ptr -> (channel : Int) -> IO Bool
checkMsgsFrom sender channel 
  = do me <- getMyVM
       msgs <- foreign FFI_C "idris_checkMessagesFrom" (Ptr -> Int -> Ptr -> IO Ptr)
                             me channel sender
       null <- nullPtr msgs
       pure (not null)

||| Check inbox for messages. If there are none, blocks until a message
||| arrives.
||| Note that this is not at all type safe! It is intended to be used in
||| a type safe wrapper.
getMsg : IO a
getMsg {a} = do me <- getMyVM
                m <- foreign FFI_C "idris_recvMessage" (Ptr -> IO Ptr) me
                MkRaw x <- foreign FFI_C "idris_getMsg" (Ptr -> IO (Raw a)) m
                pure x

||| Check inbox for messages. If there are none, blocks until a message
||| arrives. Return triple of sender's ID, channel ID, and the message.
||| Note that this is not at all type safe! It is intended to be used in
||| a type safe wrapper.
getMsgWithSender : IO (Ptr, Int, a)
getMsgWithSender {a} 
           = do me <- getMyVM
                m <- foreign FFI_C "idris_recvMessage" 
                             (Ptr -> IO Ptr) me
                MkRaw x <- foreign FFI_C "idris_getMsg" (Ptr -> IO (Raw a)) m
                vm <- sender m
                chan <- channel_id m
                foreign FFI_C "idris_freeMsg" (Ptr -> IO ()) m
                pure (vm, chan, x)

||| Check inbox for messages on a particular channel. If there are none,
||| blocks until a message arrives. Returns `Nothing` if the sender isn't
||| alive
getMsgFrom : Ptr -> (channel : Int) -> IO (Maybe a)
getMsgFrom {a} sender channel 
  = do me <- getMyVM
       m <- foreign FFI_C "idris_recvMessageFrom"
                    (Ptr -> Int -> Ptr -> IO Ptr) me channel sender
       null <- nullPtr m
       if null 
          then pure Nothing
          else do
             MkRaw x <- foreign FFI_C "idris_getMsg" (Ptr -> IO (Raw a)) m
             foreign FFI_C "idris_freeMsg" (Ptr -> IO ()) m
             pure (Just x)

stopThread : IO a
stopThread = do vm <- getMyVM
                MkRaw res <- foreign FFI_C "idris_stopThread" (Ptr -> IO (Raw a)) vm
                pure res


