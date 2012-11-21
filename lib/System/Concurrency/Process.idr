-- WARNING: No guarantees that this works properly yet! 

module System.Concurrency.Process

import System.Concurrency.Raw

%access public

abstract 
data ProcID msg = MkPID Ptr

-- Type safe message passing programs. Parameterised over the type of
-- message which can be send, and the return type.

data Process : (msgType : Set) -> Set -> Set where
     lift : IO a -> Process msg a

instance Functor (Process msg) where
     fmap f (lift a) = lift (fmap f a)

instance Applicative (Process msg) where
     pure = lift . pure
     (lift f) <$> (lift a) = lift (f <$> a)

instance Monad (Process msg) where
     (lift io) >>= k = lift (do x <- io
                                case k x of
                                     lift v => v)

run : Process msg x -> IO x
run (lift prog) = prog

-- Get current process ID

myID : Process msg (ProcID msg)
myID = lift (pure (MkPID prim__vm))

-- Send a message to another process

send : ProcID msg -> msg -> Process msg ()
send (MkPID p) m = lift (sendToThread p (prim__vm, m))

-- Return whether a message is waiting in the queue

msgWaiting : Process msg Bool
msgWaiting = lift checkMsgs 

-- Receive a message - blocks if there is no message waiting

recv : Process msg msg
recv {msg} = do (senderid, m) <- lift get
                pure m
  where get : IO (Ptr, msg)
        get = getMsg

-- receive a message, and return with the sender's process ID.

recvWithSender : Process msg (ProcID msg, msg)
recvWithSender {msg} 
     = do (senderid, m) <- lift get
          pure (MkPID senderid, m)
  where get : IO (Ptr, msg)
        get = getMsg

create : |(thread : Process msg ()) -> Process msg (ProcID msg)
create (lift p) = do ptr <- lift (fork p)
                     pure (MkPID ptr)

