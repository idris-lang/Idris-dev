-- WARNING: No guarantees that this works properly yet!

module System.Concurrency.Process

import System.Concurrency.Raw

%access public

abstract
data ProcID msg = MkPID Ptr

||| Type safe message passing programs. Parameterised over the type of
||| message which can be send, and the return type.
data Process : (msgType : Type) -> Type -> Type where
     Lift : IO a -> Process msg a

instance Functor (Process msg) where
     map f (Lift a) = Lift (map f a)

instance Applicative (Process msg) where
     pure = Lift . return
     (Lift f) <*> (Lift a) = Lift (f <*> a)

instance Monad (Process msg) where
     (Lift io) >>= k = Lift (do x <- io
                                case k x of
                                     Lift v => v)

run : Process msg x -> IO x
run (Lift prog) = prog

||| Get current process ID
myID : Process msg (ProcID msg)
myID = Lift (return (MkPID prim__vm))

||| Send a message to another process
send : ProcID msg -> msg -> Process msg ()
send (MkPID p) m = Lift (sendToThread p (prim__vm, m))

||| Return whether a message is waiting in the queue
msgWaiting : Process msg Bool
msgWaiting = Lift checkMsgs

||| Return whether a message is waiting in the queue from a specific sender
msgWaitingFrom : ProcID msg -> Process msg Bool
msgWaitingFrom (MkPID p) = Lift (checkMsgsFrom p)

||| Receive a message - blocks if there is no message waiting
recv : Process msg msg
recv {msg} = do (senderid, m) <- Lift get
                return m
  where get : IO (Ptr, msg)
        get = getMsg

||| Receive a message from specific sender - blocks if there is no message waiting
recvFrom : ProcID msg -> Process msg msg
recvFrom (MkPID p) {msg} = do (senderid, m) <- Lift get
                              return m
  where get : IO (Ptr, msg)
        get = getMsgFrom p

||| receive a message, and return with the sender's process ID.
recvWithSender : Process msg (ProcID msg, msg)
recvWithSender {msg}
     = do (senderid, m) <- Lift get
          return (MkPID senderid, m)
  where get : IO (Ptr, msg)
        get = getMsg

create : Process msg () -> Process msg (ProcID msg)
create (Lift p) = do ptr <- Lift (fork p)
                     return (MkPID ptr)
