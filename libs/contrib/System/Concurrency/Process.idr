-- WARNING: No guarantees that this works properly yet!

module System.Concurrency.Process

import System.Concurrency.Raw

%access public export

export
data ProcID msg = MkPID Ptr

||| Type safe message passing programs. Parameterised over the type of
||| message which can be send, and the return type.
data Process : (msgType : Type) -> Type -> Type where
     Lift : IO a -> Process msg a

implementation Functor (Process msg) where
     map f (Lift a) = Lift (map f a)

implementation Applicative (Process msg) where
     pure = Lift . pure
     (Lift f) <*> (Lift a) = Lift (f <*> a)

implementation Monad (Process msg) where
     (Lift io) >>= k = Lift (do x <- io
                                case k x of
                                     Lift v => v)

run : Process msg x -> IO x
run (Lift prog) = prog

||| Get current process ID
export
myID : Process msg (ProcID msg)
myID = Lift (do me <- getMyVM
                pure (MkPID me))

||| Send a message to another process
||| Returns whether the send was unsuccessful.
export
send : ProcID msg -> msg -> Process msg Bool
send (MkPID p) m = Lift (do me <- getMyVM
                            x <- sendToThread p 0 (me, m)
                            pure (x /= 0))

||| Return whether a message is waiting in the queue
export
msgWaiting : Process msg Bool
msgWaiting = Lift checkMsgs

||| Return whether a message is waiting in the queue from a specific sender
export
msgWaitingFrom : ProcID msg -> Process msg Bool
msgWaitingFrom (MkPID p) = Lift (checkMsgsFrom p 0)

||| Receive a message - blocks if there is no message waiting
export
recv : Process msg msg
recv {msg} = do (senderid, m) <- Lift get
                pure m
  where get : IO (Ptr, msg)
        get = getMsg

||| Receive a message from specific sender - blocks if there is no message waiting
||| Fails if the sender is no longer running
export
recvFrom : ProcID msg -> Process msg (Maybe msg)
recvFrom (MkPID p) {msg} = do Just (senderid, m) <- Lift get
                                 | pure Nothing
                              pure (Just m)
  where get : IO (Maybe (Ptr, msg))
        get = getMsgFrom p 0

||| receive a message, and return with the sender's process ID.
export
recvWithSender : Process msg (ProcID msg, msg)
recvWithSender {msg}
     = do (senderid, m) <- Lift get
          pure (MkPID senderid, m)
  where get : IO (Ptr, msg)
        get = getMsg

export
create : Process msg () -> Process msg (ProcID msg)
create (Lift p) = do ptr <- Lift (fork p)
                     pure (MkPID ptr)
