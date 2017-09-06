module Network.Socket.ST

import Network.Socket
import Control.ST
import CFFI.Errno

public export
data SocketState = Ready
                 | Bound
                 | Listening
                 | Open
                 | Closed

public export
data CloseOK : SocketState -> Type where
  CloseOpen : CloseOK Open
  CloseListening : CloseOK Listening

public export
interface Sockets (m : Type -> Type) where
  Sock : SocketState -> Type
  socket : ST m (Either CError Var) [addIfRight (Sock Ready)]
  bind : (sock : Var) -> (addr : Maybe SocketAddress) -> (port : Port) ->
         ST m (Either CError ()) [sock ::: Sock Ready :-> (Sock Closed `or` Sock Bound)]
  listen : (sock : Var) ->
           ST m (Either CError ()) [sock ::: Sock Bound :-> (Sock Closed `or` Sock Listening)]
  accept : (sock : Var) ->
           ST m (Either CError Var) [sock ::: Sock Listening, addIfRight (Sock Open)]
  send : (sock : Var) -> String ->
         ST m (Either CError ()) [sock ::: Sock Open :-> (Sock Closed `or` Sock Open)]
  recv : (sock : Var) ->
         ST m (Either CError String) [sock ::: Sock Open :-> (Sock Closed `or` Sock Open)]
  close : (sock : Var) ->
          {auto prf : CloseOK st} -> ST m () [sock ::: Sock st :-> Sock Closed]
  remove : (sock : Var) ->
           ST m () [Remove sock (Sock Closed)]
  connect : (sock : Var) -> SocketAddress -> Port ->
            ST m (Either CError ()) [sock ::: Sock Ready :-> (Sock Closed `or` Sock Open)]

public export
implementation Sockets IO where
  Sock _ = State Socket
  socket = do
    Right sock <- lift $ Socket.socket AF_INET Stream 0
          | Left err => do
              cerr <- lift $ getError err
              pure (Left cerr)
    lbl <- new sock
    pure $ Right lbl

  bind sock addr port = do
    err <- lift $ bind !(read sock) addr port
    if err /= 0
      then do
        cerr <- lift $ getError err
        pure $ Left cerr
      else pure $ Right ()

  listen sock = do
    err <- lift $ listen !(read sock)
    if err /= 0
      then do
        cerr <- lift $ getError err
        pure $ Left cerr
      else pure $ Right ()

  accept sock = do
    Right (conn, addr) <- lift $ accept !(read sock)
          | Left err => do
              cerr <- lift $ getError err
              pure (Left cerr)
    lbl <- new conn
    returning (Right lbl) (toEnd lbl)

  send sock str = do
    Right err <- lift $ send !(read sock) str
          | Left err => do
              cerr <- lift $ getError err
              pure (Left cerr)
    if err /= 0
      then do
        cerr <- lift $ getError err
        pure $ Left cerr
      else pure $ Right ()

  recv sock = do
    Right (str, err) <- lift $ recv !(read sock) 1024
          | Left err => do
              cerr <- lift $ getError err
              pure (Left cerr)
    if err /= 0
      then do
        cerr <- lift $ getError err
        pure $ Left cerr
      else pure $ Right str

  close sock = do
    lift $ close !(read sock)
    pure ()

  remove sock = delete sock

  connect sock addr port = do
    err <- lift $ connect !(read sock) addr port
    if err /= 0
      then do
        cerr <- lift $ getError err
        pure $ Left cerr
      else pure $ Right ()
