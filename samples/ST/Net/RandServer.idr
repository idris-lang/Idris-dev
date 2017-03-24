import Network.Socket
import Control.ST
import Control.ST.ImplicitCall
import System

import Network
import Threads

{- A random number server.

This receives requests from a client, as a number, and sends a reply
which is a random number within the requested bound.

There are two states: one for the server, and one for a connected session.
The server repeatedly listens for requests and creats a session for each
incoming request.
-}

-- States of a connected session
data SessionState = Waiting -- waiting for the client to send
                  | Processing -- calculating a response to send back
                  | Done -- received message and replied to it

interface RandomSession (m : Type -> Type) where
  -- A connected session
  Connection : SessionState -> Type
  -- A server listening for connections
  Server : Type

  -- Receive a request on a Waiting connection. If there is a request
  -- available, move to the Processing state
  recvReq : (conn : Var) ->
            ST m (Maybe Integer) 
                 [conn ::: Connection Waiting :->
                           \res => Connection (case res of
                                                    Nothing => Done
                                                    Just _ => Processing)]
  -- Send a reply, and move the connection to the Done state
  sendResp : (conn : Var) -> Integer ->
             ST m () [conn ::: Connection Processing :-> Connection Done]

  -- Create a server
  start : ST m (Maybe Var) [addIfJust Server]
  -- Close a server
  quit : (srv : Var) -> ST m () [Remove srv Server]
  -- Finish a connection
  done : (conn : Var) -> ST m () [Remove conn (Connection Done)]

  -- Listen for an incoming connection. If there is one, create a session
  -- with a connection in the Waiting state
  accept : (srv : Var) ->
           ST m (Maybe Var) 
                [srv ::: Server, addIfJust (Connection Waiting)]

interface Sleep (m : Type -> Type) where
  usleep : (i : Int) -> { auto prf : So (i >= 0 && i <= 1000000) } -> 
           STrans m () xs (const xs)

Sleep IO where
  usleep x = lift (System.usleep x)


using (Sleep io, ConsoleIO io, RandomSession io, Conc io)
  rndSession : (conn : Var) -> 
               ST io () [Remove conn (Connection {m=io} Waiting)]
  rndSession conn =
         do Just bound <- call (recvReq conn)
              | Nothing => do putStr "Nothing received\n"
                              call (done conn)
            putStr "Calculating reply...\n"
            usleep 1000000
            sendResp conn bound -- (seed `mod` (bound + 1))
            call (done conn)

  rndLoop : (srv : Var) -> ST io () [srv ::: Server {m=io}]
  rndLoop srv 
    = do Just conn <- accept srv
              | Nothing => putStr "accept failed\n"
         putStr "Connection received\n"
         fork (rndSession conn)
         rndLoop srv

  rndServer : ST io () []
  rndServer 
    = do Just srv <- start
              | Nothing => putStr "Can't start server\n"
         call (rndLoop srv)
         quit srv

implementation (ConsoleIO io, Sockets io) => RandomSession io where
  
  -- Connections and servers are composite states, so to implement things
  -- in terms of them we need to 'split' at the state and 'combine' at the
  -- end, in every method
  Connection Waiting = Composite [State Integer, Sock {m=io} Open]
  Connection Processing = Composite [State Integer, Sock {m=io} Open]
  Connection Done = Composite [State Integer, Sock {m=io} Closed]

  Server = Composite [State Integer, Sock {m=io} Listening]

  recvReq rec = do [seed, conn] <- split rec
                   Right msg <- recv conn
                         | Left err => do combine rec [seed, conn]
                                          pure Nothing
                   putStr ("Incoming " ++ show msg ++ "\n")
                   combine rec [seed, conn]
                   pure (Just (cast msg))

  sendResp rec val = do [seed, conn] <- split rec
                        Right () <- send conn (cast (!(read seed) `mod` val) ++ "\n")
                              | Left err => do combine rec [seed, conn]
                                               pure ()
                        close conn
                        combine rec [seed, conn]
  
  start = do srv <- new ()
             Right sock <- socket Stream
                   | Left err => do delete srv; pure Nothing
             Right () <- bind sock Nothing 9442
                   | Left err => do call (remove sock)
                                    delete srv
                                    pure Nothing
             Right () <- listen sock
                   | Left err => do call (remove sock)
                                    delete srv
                                    pure Nothing
             putStr "Started server\n"
             seed <- new 12345
             combine srv [seed, sock]
             pure (Just srv)
  
  quit srv = do [seed, sock] <- split srv -- need to delete everything
                close sock; remove sock; delete seed; delete srv
  done conn = do [seed, sock] <- split conn -- need to delete connection data
                 remove sock; delete seed; delete conn
  
  accept srv = do [seed, sock] <- split srv
                  seedVal <- read seed
                  write seed ((1664525 * seedVal + 1013904223) 
                                `prim__sremBigInt` (pow 2 32))
                  Right conn <- accept sock
                        | Left err => do combine srv [seed, sock]
                                         pure Nothing -- no incoming message
                  -- We're sending the seed to the child process and keeping
                  -- a copy ourselves, so we need to explicitly make a new
                  -- one
                  rec <- new ()
                  seed' <- new seedVal
                  combine rec [seed', conn]
                  combine srv [seed, sock]
                  toEnd rec
                  pure (Just rec)

main : IO ()
main = run rndServer

