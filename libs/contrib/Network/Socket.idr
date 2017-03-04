||| Low-Level C Sockets bindings for Idris. Used by higher-level, cleverer things.
|||
||| Original (C) SimonJF, MIT Licensed, 2014
||| Modified (C) The Idris Community, 2015, 2016
module Network.Socket

import public Network.Socket.Data
import Network.Socket.Raw

%include C "idris_net.h"
%include C "sys/types.h"
%include C "sys/socket.h"
%include C "netdb.h"

%access export

-- ----------------------------------------------------- [ Network Socket API. ]

||| Creates a UNIX socket with the given family, socket type and protocol
||| number. Returns either a socket or an error.
socket : (fam  : SocketFamily)
      -> (ty   : SocketType)
      -> (pnum : ProtocolNumber)
      -> IO (Either SocketError Socket)
socket sf st pn = do
  socket_res <- foreign FFI_C "socket"
                        (Int -> Int -> Int -> IO Int)
                        (toCode sf) (toCode st) pn

  if socket_res == -1
    then map Left getErrno
    else pure $ Right (MkSocket socket_res sf st pn)

||| Close a socket
close : Socket -> IO ()
close sock = foreign FFI_C "close" (Int -> IO ()) (descriptor sock)

||| Binds a socket to the given socket address and port.
||| Returns 0 on success, an error code otherwise.
bind : (sock : Socket)
    -> (addr : Maybe SocketAddress)
    -> (port : Port)
    -> IO Int
bind sock addr port = do
    bind_res <- foreign FFI_C "idrnet_bind"
                    (Int -> Int -> Int -> String -> Int -> IO Int)
                    (descriptor sock) (toCode $ family sock)
                    (toCode $ socketType sock) (saString addr) port
    if bind_res == (-1)
      then getErrno
      else pure 0
  where
    saString : Maybe SocketAddress -> String
    saString (Just sa) = show sa
    saString Nothing   = ""

||| Connects to a given address and port.
||| Returns 0 on success, and an error number on error.
connect : (sock : Socket)
       -> (addr : SocketAddress)
       -> (port : Port)
       -> IO ResultCode
connect sock addr port = do
  conn_res <- foreign FFI_C "idrnet_connect"
                  (Int -> Int -> Int -> String -> Int -> IO Int)
                  (descriptor sock) (toCode $ family sock) (toCode $ socketType sock) (show addr) port

  if conn_res == (-1)
    then getErrno
    else pure 0

||| Listens on a bound socket.
|||
||| @sock The socket to listen on.
listen : (sock : Socket) -> IO Int
listen sock = do
  listen_res <- foreign FFI_C "listen" (Int -> Int -> IO Int)
                    (descriptor sock) BACKLOG
  if listen_res == (-1)
    then getErrno
    else pure 0

||| Accept a connection on the provided socket.
|||
||| Returns on failure a `SocketError`
||| Returns on success a pairing of:
||| + `Socket`        :: The socket representing the connection.
||| + `SocketAddress` :: The
|||
||| @sock The socket used to establish connection.
accept : (sock : Socket)
      -> IO (Either SocketError (Socket, SocketAddress))
accept sock = do

  -- We need a pointer to a sockaddr structure. This is then passed into
  -- idrnet_accept and populated. We can then query it for the SocketAddr and free it.

  sockaddr_ptr <- foreign FFI_C "idrnet_create_sockaddr"
                          (IO Ptr)

  accept_res <- foreign FFI_C "idrnet_accept"
                        (Int -> Ptr -> IO Int)
                        (descriptor sock) sockaddr_ptr
  if accept_res == (-1)
    then map Left getErrno
    else do
      let (MkSocket _ fam ty p_num) = sock
      sockaddr <- getSockAddr (SAPtr sockaddr_ptr)
      sockaddr_free (SAPtr sockaddr_ptr)
      pure $ Right ((MkSocket accept_res fam ty p_num), sockaddr)

||| Send data on the specified socket.
|||
||| Returns on failure a `SocketError`.
||| Returns on success the `ResultCode`.
|||
||| @sock The socket on which to send the message.
||| @msg  The data to send.
send : (sock : Socket)
    -> (msg  : String)
    -> IO (Either SocketError ResultCode)
send sock dat = do
  send_res <- foreign FFI_C "idrnet_send"
                      (Int -> String -> IO Int)
                      (descriptor sock) dat

  if send_res == (-1)
    then map Left getErrno
    else pure $ Right send_res

||| Receive data on the specified socket.
|||
||| Returns on failure a `SocketError`
||| Returns on success a pairing of:
||| + `String`     :: The payload.
||| + `ResultCode` :: The result of the underlying function.
|||
||| @sock The socket on which to receive the message.
||| @len  How much of the data to send.
recv : (sock : Socket)
    -> (len : ByteLength)
    -> IO (Either SocketError (String, ResultCode))
recv sock len = do
  -- Firstly make the request, get some kind of recv structure which
  -- contains the result of the recv and possibly the retrieved payload
  recv_struct_ptr <- foreign FFI_C "idrnet_recv"
                             (Int -> Int -> IO Ptr)
                             (descriptor sock) len
  recv_res <- foreign FFI_C "idrnet_get_recv_res"
                      (Ptr -> IO Int)
                      recv_struct_ptr

  if recv_res == (-1)
    then do
      errno <- getErrno
      freeRecvStruct (RSPtr recv_struct_ptr)
      pure $ Left errno
    else
      if recv_res == 0
        then do
           freeRecvStruct (RSPtr recv_struct_ptr)
           pure $ Left 0
        else do
           payload <- foreign FFI_C "idrnet_get_recv_payload"
                             (Ptr -> IO String)
                             recv_struct_ptr
           freeRecvStruct (RSPtr recv_struct_ptr)
           pure $ Right (payload, recv_res)

||| Send a message.
|||
||| Returns on failure a `SocketError`
||| Returns on success the `ResultCode`
|||
||| @sock The socket on which to send the message.
||| @addr Address of the recipient.
||| @port The port on which to send the message.
||| @msg  The message to send.
sendTo : (sock : Socket)
      -> (addr : SocketAddress)
      -> (port : Port)
      -> (msg  : String)
      -> IO (Either SocketError ByteLength)
sendTo sock addr p dat = do
  sendto_res <- foreign FFI_C "idrnet_sendto"
                   (Int -> String -> String -> Int -> Int -> IO Int)
                   (descriptor sock) dat (show addr) p (toCode $ family sock)

  if sendto_res == (-1)
    then map Left getErrno
    else pure $ Right sendto_res

||| Receive a message.
|||
||| Returns on failure a `SocketError`.
||| Returns on success a triple of
||| + `UDPAddrInfo` :: The address of the sender.
||| + `String`      :: The payload.
||| + `Int`         :: Result value from underlying function.
|||
||| @sock The channel on which to receive.
||| @len  Size of the expected message.
|||
recvFrom : (sock : Socket)
        -> (len  : ByteLength)
        -> IO (Either SocketError (UDPAddrInfo, String, ResultCode))
recvFrom sock bl = do
  recv_ptr <- foreign FFI_C "idrnet_recvfrom"
                (Int -> Int -> IO Ptr)
                (descriptor sock) bl

  let recv_ptr' = RFPtr recv_ptr

  if !(nullPtr recv_ptr)
    then map Left getErrno
    else do
      result <- foreign FFI_C "idrnet_get_recvfrom_res"
                        (Ptr -> IO Int)
                        recv_ptr
      if result == -1
        then do
          freeRecvfromStruct recv_ptr'
          map Left getErrno
        else do
          payload <- foreignGetRecvfromPayload recv_ptr'
          port <- foreignGetRecvfromPort recv_ptr'
          addr <- foreignGetRecvfromAddr recv_ptr'
          freeRecvfromStruct recv_ptr'
          pure $ Right (MkUDPAddrInfo addr port, payload, result)

