module System.Concurrency.Channels

import System.Concurrency.Raw

||| A Channel is a connection between two processes. Channels can be created
||| either using 'listen' to wait for an incoming connection, or 'connect'
||| which initiates a connection to another process.
||| Channels cannot (yet) be passed between processes.
export
data Channel : Type where
     MkConc : (pid : Ptr) -> (ch_id : Int) -> Channel

||| A PID is a process identifier, as returned by `spawn`
export
data PID : Type where
     MkPID : (pid : Ptr) -> PID

||| Spawn a process in a new thread, returning the process ID
||| Returns `Nothing` if there are not enough resources to create the new thread
export
spawn : (process : IO ()) -> IO (Maybe PID)
spawn proc = do pid <- fork proc
                if !(nullPtr pid)
                   then pure Nothing
                   else pure (Just (MkPID pid))

||| Create a channel which connects this process to another process
export
connect : (pid : PID) -> IO (Maybe Channel)
connect (MkPID pid) = do ch_id <- sendToThread pid 0 ()
                         if (ch_id /= 0)
                            then pure (Just (MkConc pid ch_id))
                            else pure Nothing

||| Listen for incoming connections. If another process has initiated a
||| communication with this process, returns a channel 
export
listen : (timeout : Int) -> IO (Maybe Channel)
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
unsafeSend : Channel -> (val : a) -> IO Bool
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
unsafeRecv : (expected : Type) -> Channel -> IO (Maybe expected)
unsafeRecv a (MkConc pid ch_id) = getMsgFrom {a} pid ch_id

||| Exit the thread immediately
export
stopThread : IO a
stopThread = Raw.stopThread 
