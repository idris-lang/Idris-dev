module System.Concurrency.Sessions

import System.Concurrency.Raw

||| A Session is a connection between two processes. Sessions can be created
||| either using 'listen' to wait for an incoming connection, or 'connect'
||| which initiates a connection to another process.
||| Sessions cannot be passed between processes.
export
data Session : Type where
     MkConc : (pid : Ptr) -> (ch_id : Int) -> Session

||| A PID is a process identifier, as returned by `spawn`
export
data PID : Type where
     MkPID : (pid : Ptr) -> PID

||| Spawn a process in a new thread, returning the process ID
export
spawn : IO () -> IO PID
spawn proc = do pid <- fork proc
                pure (MkPID pid)

||| Create a channel which connects this process to another process
export
connect : (proc : PID) -> IO (Maybe Session)
connect (MkPID pid) = do ch_id <- sendToThread pid 0 ()
                         if (ch_id /= 0)
                            then pure (Just (MkConc pid ch_id))
                            else pure Nothing

||| Listen for incoming connections. If another process has initiated a
||| communication with this process, returns a channel 
export
listen : (timeout : Int) -> IO (Maybe Session)
listen timeout = do checkMsgsTimeout timeout
                    Just (client, ch_id) <- listenMsgs
                       | Nothing => pure Nothing
                    getMsgFrom {a = ()} client ch_id -- remove init message
                    pure (Just (MkConc client ch_id))

||| Send a message on a channel. Returns whether the message was successfully
||| sent to the process at the other end of the channel. This will fail if
||| the process on the channel is no longer running.
||| This is unsafe because there is no type checking, so there must be
||| a protocol (externally checked) which ensures that the message send
||| is of type expected by the receiver.
export
unsafeSend : Session -> (val : a) -> IO Bool
unsafeSend (MkConc pid ch_id) val
     = do ok <- sendToThread pid ch_id val
          pure (ok /= 0)

||| Receive a message on a channel, with an explicit type.
||| Blocks if there is nothing to receive. Returns `Nothing` if the
||| process on the channel is no longer running.
||| This is unsafe because there is no type checking, so there must be
||| a protocol (externally checked) which ensures that the message received
||| is of the type given by the sender.
export
unsafeRecv : (a : Type) -> Session -> IO (Maybe a)
unsafeRecv a (MkConc pid ch_id) = getMsgFrom {a} pid ch_id

