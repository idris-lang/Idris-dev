module Process

import System.Concurrency.Raw
import public Data.List -- public, to get proof search machinery

%access public export

-- Process IDs are parameterised by their interface. A request of type
-- 'iface t' will get a response of type 't'
data ProcID : (iface : Type -> Type) -> Type where
     MkPID : Ptr -> ProcID iface

data ServerID : Type where
     MkServer : ProcID iface -> ServerID

implicit MkServer' : ProcID iface -> ServerID
MkServer' = MkServer

data Replied = YesR | NoR

data ReqHandle = MkReqH Nat

-- Current state of a process includes:
--   * the servers it currently has an open connection to
--   * the number of clients it currently has connected
--   * whether it has responded to a request yet

-- Therefore, we can write process types which make clear that a process
-- cannot quit while it is talking to a server, or while it still has clients
-- expecting to communicate with it, or if it has not serviced any requests.
data ProcState : Type where
     MkProcState : (servers : List ServerID) -> 
                   (clients : Nat) ->
                   Replied ->
                   ProcState 

data Pending : ReqHandle -> List (ReqHandle, Type) -> Type -> Type where
     PendingHere : Pending h ((h, t) :: hs) t
     PendingThere : Pending h hs t -> Pending h ((h', t') :: hs) t

dropPending : (hs : List (ReqHandle, Type)) -> Pending h hs ty -> 
              List (ReqHandle, Type)
dropPending ((h, t) :: xs) PendingHere = xs
dropPending ((h', t') :: xs) (PendingThere x) 
     = ((h', t') :: dropPending xs x)

data ConnectedTo : ServerID -> ProcState -> Type where
     IsConnectedTo : Elem p servers -> 
                     ConnectedTo p (MkProcState servers c reply)

data NoClient : ProcState -> Type where
     IsNoClient : NoClient (MkProcState servers 0 reply)

data OneClient : ProcState -> Type where
     IsOneClient : OneClient (MkProcState servers (S k) reply)

data Reply : ProcState -> Type where
     IsReply : Reply (MkProcState s c YesR)

data NoReply : ProcState -> Type where
     IsNoReply : NoReply (MkProcState s c NoR)

{-- Some useful operations on process state --}
newClient : ProcState -> ProcState 
newClient (MkProcState servers clients r) 
         = MkProcState servers (S clients) r

setClients : ProcState -> Nat -> ProcState 
setClients (MkProcState servers clients r) k 
          = MkProcState servers k r

newServer : ProcID iface -> ProcState -> ProcState 
newServer p (MkProcState servers clients r) 
           = MkProcState (MkServer p :: servers) clients r

dropServer : (pid : ProcID iface) -> (p : ProcState) -> 
             ConnectedTo (MkServer pid) p -> ProcState
dropServer pid (MkProcState servers c r) (IsConnectedTo prf) 
         = MkProcState (dropElem servers prf) c r

{-
pendingReq : ProcID iface -> (h : ReqHandle) -> iface t -> 
             ProcState hs -> ProcState ((h, t) :: hs)
pendingReq {t} p h x (MkProcState s c r) = MkProcState s c r

doneReq : ProcState hs -> (p : Pending h hs) -> ProcState (dropPending hs p)
doneReq (MkProcState s c r) p = MkProcState s c r
-}

replied : ProcState -> ProcState 
replied (MkProcState servers clients r) 
        = MkProcState servers clients YesR

resetReplied : ProcState -> ProcState
resetReplied (MkProcState servers clients r) 
        = MkProcState servers clients NoR

runningServer : Nat -> ProcState
runningServer c = MkProcState [] (S c) NoR

doneServer : ProcState 
doneServer = MkProcState [] 0 YesR

init : List ServerID -> ProcState 
init s = MkProcState s 0 NoR

{-- Processes themselves.

A process returns some type 'a', responds to requests on the interface
'iface', and has an input and output state.
--}
mutual
  data Process : (a : Type) -> (iface : Type -> Type) -> 
                 List (ReqHandle, Type) -> (a -> List (ReqHandle, Type)) ->
                 ProcState -> (a -> ProcState) ->
                 Type where
     -- Some plumbing
     Lift' : IO a -> Process a iface hs (const hs) p (const p)
     Pure : a -> Process a iface hs (const hs) p (const p)
     Quit : a -> Process a iface hs (const hs) p (const (resetReplied p))

     Bind : Process a iface hs hs' p p' -> 
            ((x : a) -> Process b iface (hs' x) hs'' (p' x) p'') ->
            Process b iface hs hs'' p p''

     Fork : Process () serveri [] (const []) (runningServer 1) (const Process.doneServer) ->
            Process (ProcID serveri) iface hs (const hs) p (\res => (newServer res p))
     Work : (worker : (pid : ProcID iface) -> Worker [pid] ()) ->
            (waiter : Process t iface hs (const hs) (runningServer 1) (const Process.doneServer)) ->
            Process t iface hs (const hs) p (const p)

     Request : (r : ProcID serveri) -> (x : serveri ty) ->
               {auto connected : ConnectedTo (MkServer r) p} ->
               Process ReqHandle iface 
                       hs (\h => (h, ty) :: hs)
                       p (const p)

     GetReply : (h : ReqHandle) ->
                {auto pending : Pending h hs ty} ->
                Process ty iface 
                        hs (const (dropPending hs pending))
                        p (const p)

     TimeoutRespond : (timeout : Int) ->
                      (def : res) ->
                      ({t : Type} -> (x : iface t) -> 
                                     Response (t, res) iface hs p) ->
                      Process res iface hs (const hs) p (const (replied p))

     Respond : ({t : Type} -> (x : iface t) -> 
                              Response (t, res) iface hs p) ->
               Process res iface hs (const hs) p (const (replied p))

     Connect : (r : ProcID serveri) -> 
               Process Bool iface 
                       hs (const hs)
                       p (\ok => case ok of
                                      True => newServer r p
                                      False => p)

     Disconnect : (r : ProcID serveri) ->
                  {auto connected : ConnectedTo (MkServer r) p} ->
                  Process () iface 
                          hs (const hs)
                          p (const (dropServer r p connected))

     CountClients : Process Nat iface hs (const hs) p (\n => setClients p n)

     -- FIXME: The process had better be guaranteed to change the system
     -- state (e.g. finish with a YesR since it starts with a NoR) because
     -- then it can't be used in a Respond, so responding can't loop.
     Loop : Inf (Process t iface hs hs' (resetReplied p) p') -> 
            Process t iface hs hs' p p'

  -- 'Running a iface' is the type of a process which is currently
  -- responding to requests (i.e. knows it has at least one client connected)
  -- and will not exit unless there are no clients connected
  Running : Type -> (iface : Type -> Type) -> Type
  Running a iface = {k : Nat} -> Process a iface [] (const []) (runningServer k) (const doneServer)

  Response : Type -> (iface : Type -> Type) -> List (ReqHandle, Type) ->
                     ProcState -> Type
  Response a iface hs p =  Process a iface hs (const hs) p (const p)

  -- 'Program a' is the type of a process which does not respond to any requests
  -- and begins and ends with no connections to any server open.
  Program : Type -> (iface : Type -> Type) -> Type
  Program a iface = Process a iface [] (const []) (init []) (const (init []))

  -- 'Connected s a' is the type of a process which does not respond to any 
  -- requests and begins and ends with connections to a given server list. 
  Connected : List ServerID -> Type -> Type
  Connected s a = Process a (const Void) [] (const []) (init s) (const (init s))

  -- 'Worker s a' is the type of a process which does not respond to any 
  -- requests, and begins with a connection to a server it is to send a
  -- notification to.
  Worker : List ServerID -> Type -> Type
  Worker s a = Process a (const Void) [] (const []) (init s) (const (init []))

implicit 
Lift : IO a -> Process a iface hs (const hs) p (const p) 
Lift = Lift'
     
%no_implicit -- helps error messages, and speeds things up a bit 
%inline -- so that the productivity checker treats 'bind' as a constructor!
(>>=) : Process a iface hs hs' p p' -> 
        ((x : a) -> Process b iface (hs' x) hs'' (p' x) p'') ->
        Process b iface hs hs'' p p''
(>>=) = Bind

TrySend : (proc : ProcID iface) -> iface ty -> 
          Process (Maybe ty) iface' 
                  hs (const hs)
                  (MkProcState s c r) (const (MkProcState s c r))
TrySend pid req = do True <- Connect pid | False => Pure Nothing
                     h <- Request pid req
                     resp <- GetReply h
                     Disconnect pid
                     Pure (Just resp)

Send : (proc : ProcID iface) -> iface ty -> 
       {auto prf : Elem (MkServer proc) s} ->
       Process ty iface'
               hs (const hs)
               (MkProcState s c r) (const (MkProcState s c r))
Send pid req = do h <- Request pid req
                  GetReply h

{--- evaluator --}

-- The evaluator keeps track of the number of client connections open,
-- and manages Connect/Disconnect requests by managing them whenever a
-- 'Respond' or 'TimeoutRespond' is encountered.

data MessageQ : (Type -> Type) -> Type where
     ConnectMsg : MessageQ iface
     CloseMsg : MessageQ iface
     RequestMsg : Nat -> iface t -> MessageQ iface

data MessageR : Type -> Type where
     ReplyMsg : Nat -> (ans : ty) -> MessageR ty

data Message : (Type -> Type) -> List (ReqHandle, Type) -> Type where
     MsgQuery : MessageQ iface -> Message iface hs
     MsgReply : (reply : MessageR ty) -> Message iface hs

readMsg : IO (Maybe (Ptr, Message iface hs))
readMsg {iface} {hs} = 
   do if !checkMsgs
      then do (p, _, msg) <- getMsgWithSender {a = Message iface hs}
              pure (Just (p, msg))
      else pure Nothing

readMsgTimeout : Int -> IO (Maybe (Ptr, Message iface hs))
readMsgTimeout {iface} {hs} i = 
   do if !(checkMsgsTimeout i)
      then do (pid, _, msg) <- getMsgWithSender {a = Message iface hs}
              pure (Just (pid, msg))
      else pure Nothing

data RespEnv : List (ReqHandle, Type) -> Type where
     Nil : RespEnv []
     (::) : Maybe ty -> RespEnv hs -> RespEnv ((h, ty) :: hs)

record EvalState (iface : Type -> Type) (hs : List (ReqHandle, Type)) where
  constructor MkEvalState
  queue : List (Ptr, MessageQ iface)
  reply : RespEnv hs 
  clients : Nat
  nexthandle : Nat

lookup : Pending h hs ty -> RespEnv hs -> Maybe ty
lookup PendingHere (x :: xs) = x 
lookup (PendingThere p) (x :: xs) = lookup p xs

dropResp : (pending : Pending h hs ty) -> 
           RespEnv hs -> RespEnv (dropPending hs pending)
dropResp PendingHere (x :: xs) = xs
dropResp (PendingThere p) (x :: xs) = x :: dropResp p xs

updateReplies : Pending h hs ty -> ty -> RespEnv hs -> RespEnv hs
updateReplies PendingHere msg (x :: xs) = Just msg :: xs
updateReplies (PendingThere p) msg (x :: xs) = x :: updateReplies p msg xs

total
findPending : (h : ReqHandle) -> RespEnv hs -> Maybe (ty ** Pending h hs ty)
findPending {hs = []} k [] = Nothing
findPending {hs = ((MkReqH h, t) :: hs)} (MkReqH k) (x :: xs) with (decEq h k)
  findPending {hs = ((MkReqH h, t) :: hs)} (MkReqH h) (x :: xs) | (Yes Refl) 
       = Just (t ** PendingHere)
  findPending {hs = ((MkReqH h, t) :: hs)} (MkReqH k) (x :: xs) | (No contra) 
       = do (ty' ** p') <- findPending (MkReqH k) xs
            Just (ty' ** PendingThere p')

covering
updateQueue : EvalState iface hs -> IO (EvalState iface hs)
updateQueue {iface} {hs} st 
  = case !(readMsg {iface} {hs}) of
         Nothing => pure st
         Just (pid, MsgQuery msg) => 
              updateQueue (record { queue = queue st ++ [(pid, msg)] } st)
         Just (pid, MsgReply (ReplyMsg rq ans)) => 
              case findPending (MkReqH rq) (reply st) of
                   Nothing => updateQueue {iface} {hs} st -- can't happen!
                   Just (ty ** pend) => 
                        updateQueue (record { reply = updateReplies pend (believe_me ans) (reply st) } st)

-- Keep updating the queue with incoming messages until either we get a 
-- RequestMsg, or we reach a timeout.
covering
updateQueueTimeout : Int -> EvalState iface hs -> IO (EvalState iface hs)
updateQueueTimeout {iface} {hs} i st 
  = case !(readMsgTimeout {iface} {hs} i) of
         Nothing => pure st
         Just (pid, MsgQuery (RequestMsg rq msg)) => 
              pure (record { queue = queue st ++ [(pid, RequestMsg rq msg)] } st)
         Just (pid, MsgQuery msg) => do
              -- TODO: Why not update client count here too?
              updateQueueTimeout i (record { queue = queue st ++ [(pid, msg)] } st)
         Just (pid, MsgReply (ReplyMsg rq ans)) => 
              case findPending (MkReqH rq) (reply st) of
                   Nothing => updateQueueTimeout i {iface} {hs} st -- can't happen!
                   Just (ty ** pend) => 
                        updateQueueTimeout i (record { reply = updateReplies pend (believe_me ans) (reply st) } st)

total
removeReq : List (Ptr, MessageQ iface) -> List (Ptr, MessageQ iface) -> 
             Maybe (Ptr, (ty ** (Nat, iface ty)), List (Ptr, MessageQ iface))
removeReq acc [] = Nothing
removeReq acc ((pid, RequestMsg rq m) :: xs) = Just (pid, (_ ** (rq, m)), reverse acc ++ xs)
removeReq acc (x :: xs) = removeReq (x :: acc) xs

total
removeConn : Nat ->
             List (Ptr, MessageQ iface) -> List (Ptr, MessageQ iface) -> 
             (Nat, List (Ptr, MessageQ iface))
removeConn cl acc [] = (cl, reverse acc)
removeConn cl acc ((pid, ConnectMsg) :: xs) 
     = removeConn (cl + 1) acc xs
removeConn cl acc ((pid, CloseMsg) :: xs) 
     = removeConn (minus cl 1) acc xs
removeConn cl acc (x :: xs) = removeConn cl (x :: acc) xs

-- Remove the first thing in the event list which is a request, if it
-- exists.
getRequest :  EvalState iface hs -> Maybe (Ptr, (ty ** (Nat, iface ty)), EvalState iface hs)
getRequest (MkEvalState queue reply clients nh) 
     = do (pid, req, queue') <- removeReq [] queue
          pure (pid, req, MkEvalState queue' reply clients nh)

countClients : EvalState iface hs -> (Nat, EvalState iface hs)
countClients (MkEvalState queue reply clients nh) 
     = let (clients', queue') = removeConn clients [] queue in
           (clients', MkEvalState queue' reply clients' nh)

-- sendResponse : Ptr -> 
--                (ty -> EvalState iface hs -> IO a) -> 
--                (x, ty) -> EvalState iface hs -> 
--                IO a
-- sendResponse {iface} {hs} pid k (resp, val) st = do
--        sendToThread pid (MsgReply {hs} {iface} ?prf (ReplyMsg resp))
--        k val st

covering
eval : EvalState iface hs -> 
       {p : ProcState} -> {p' : ty -> ProcState} ->
       Process ty iface hs hs' p p' ->
       ((res : ty) -> EvalState iface (hs' res) -> IO a) -> IO a
eval st (Lift' x) k = do x' <- x
                         k x' st
eval st (Pure x) k = k x st
eval st (Quit x) k = k x st
eval st (Bind x f) k = eval st x (\x', st' => eval st' (f x') k)

eval st (Fork proc) k 
        = do ptr <- fork (eval (MkEvalState [] [] 1 0) proc (\_, _ => pure ()))
             k (MkPID ptr) st 

eval st (Work proc cont) k 
        = do me <- getMyVM
             ptr <- fork (eval (MkEvalState [] [] 0 0) (proc (MkPID me))
                               (\_, _ => pure ()))
             eval (record { clients = clients st + 1 } st) cont k

eval {hs} (MkEvalState q reqs c nh) (Request (MkPID pid) x) k
     = do sendToThread pid 0 (MsgQuery {hs} (RequestMsg nh x))
          k (MkReqH nh) (MkEvalState q (Nothing :: reqs) c (S nh))

eval {p} st (GetReply {pending} h) k 
      = do -- Need to keep receiving messages until there's a response 
           -- available
           MkEvalState q reqs c nh <- updateQueue st
           case lookup pending reqs of
                Nothing => do checkMsgsTimeout 1
                              eval {p} (MkEvalState q reqs c nh) (GetReply h) k
                Just reply => 
                    k reply (MkEvalState q (dropResp pending reqs) c nh)

eval {iface} {hs} st (TimeoutRespond timeout def f) k 
      = do st' <- updateQueueTimeout timeout st
           case getRequest st' of
                Nothing => k def st'
                Just (pid, (_ ** (rq, req)), st'') => do 
                     eval st'' (f req) -- (sendResponse pid k) -- ?foo 
                       -- this weirdness works around an erasure bug
                       -- which causes a seg fault...
                       (\ r, st''' => 
                            case r of
                               (resp, val) => do
                                  sendToThread pid 0 (MsgReply {iface} {hs} (ReplyMsg rq resp))
                                  k val st''')

eval {iface} {hs} st (Respond f) k 
      = do st' <- updateQueue st
           case getRequest st' of
                Nothing => eval {iface} st' (Respond f) k
                Just (pid, (_ ** (rq, req)), st'') => do
                     eval st'' (f req) (\ (resp, val), st''' => do
                       sendToThread pid 0 (MsgReply {iface} {hs} (ReplyMsg rq resp))
                       k val st''')

eval {hs} st (Connect {serveri} (MkPID pid)) k 
     = do me <- getMyVM
          if pid == me then k False st else do
            v <- sendToThread pid 0 (MsgQuery {iface=serveri} {hs}
                                              ConnectMsg)
            -- TODO: Wait for ACK
            k (v == 1) st

eval {hs} st (Disconnect {serveri} (MkPID pid)) k 
     = do v <- sendToThread pid 0 (MsgQuery {iface=serveri} {hs} 
                                            CloseMsg)
          k () st

eval st CountClients k 
     = do st' <- updateQueue st
          let (cl, st'') = countClients st'
          k cl st''

eval st (Loop x) k = eval st x k

run : Program a iface -> IO a
run p = eval (MkEvalState [] [] 0 0) p (\res, t => pure res)
