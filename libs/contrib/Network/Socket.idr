-- Time to do this properly.
-- Low-Level C Sockets bindings for Idris. Used by higher-level, cleverer things.
-- (C) SimonJF, MIT Licensed, 2014
module IdrisNet.Socket

%include C "idris_net.h"
%include C "sys/types.h"
%include C "sys/socket.h"
%include C "netdb.h"

%access public

ByteLength : Type
ByteLength = Int

class ToCode a where
  toCode : a -> Int

||| Socket Families
|||
||| The ones that people might actually use. We're not going to need US
||| Government proprietary ones.
data SocketFamily =
  ||| Unspecified
  AF_UNSPEC |
  ||| IP / UDP etc. IPv4
  AF_INET |
  |||  IP / UDP etc. IPv6
  AF_INET6

instance Show SocketFamily where
  show AF_UNSPEC = "AF_UNSPEC"
  show AF_INET   = "AF_INET"
  show AF_INET6  = "AF_INET6"

instance ToCode SocketFamily where
  toCode AF_UNSPEC = 0
  toCode AF_INET   = 2
  toCode AF_INET6  = 10

getSocketFamily : Int -> Maybe SocketFamily
getSocketFamily i = Prelude.List.lookup i [(0, AF_UNSPEC), (2, AF_INET), (10, AF_INET6)]

||| Socket Types.
data SocketType =
  ||| Not a socket, used in certain operations
  NotASocket |
  ||| TCP
  Stream |
  ||| UDP
  Datagram |
  ||| Raw sockets
  RawSocket

instance Show SocketType where
  show NotASocket = "Not a socket"
  show Stream     = "Stream"
  show Datagram   = "Datagram"
  show RawSocket  = "Raw"

instance ToCode SocketType where
  toCode NotASocket = 0
  toCode Stream     = 1
  toCode Datagram   = 2
  toCode RawSocket  = 3


data RecvStructPtr = RSPtr Ptr
data RecvfromStructPtr = RFPtr Ptr
data BufPtr = BPtr Ptr
data SockaddrPtr = SAPtr Ptr

||| Protocol Number.
|||
||| Generally good enough to just set it to 0.
ProtocolNumber : Type
ProtocolNumber = Int

||| SocketError: Error thrown by a socket operation
SocketError : Type
SocketError = Int

||| SocketDescriptor: Native C Socket Descriptor
SocketDescriptor : Type
SocketDescriptor = Int

data SocketAddress = IPv4Addr Int Int Int Int
                   | IPv6Addr -- Not implemented (yet)
                   | Hostname String
                   | InvalidAddress -- Used when there's a parse error

instance Show SocketAddress where
  show (IPv4Addr i1 i2 i3 i4) = concat $ Prelude.List.intersperse "." (map show [i1, i2, i3, i4])
  show IPv6Addr = "NOT IMPLEMENTED YET"
  show (Hostname host) = host
  show InvalidAddress = "Invalid"

Port : Type
Port = Int

||| Backlog used within listen() call -- number of incoming calls
BACKLOG : Int
BACKLOG = 20

-- FIXME: This *must* be pulled in from C
EAGAIN : Int 
EAGAIN = 11

-- TODO: Expand to non-string payloads
record UDPRecvData where
  constructor MkUDPRecvData
  remote_addr : SocketAddress
  remote_port : Port
  recv_data : String
  data_len : Int

record UDPAddrInfo where
  constructor MkUDPAddrInfo
  remote_addr : SocketAddress
  remote_port : Port

||| Frees a given pointer
public
sock_free : BufPtr -> IO ()
sock_free (BPtr ptr) = foreign FFI_C "idrnet_free" (Ptr -> IO ()) ptr

public
sockaddr_free : SockaddrPtr -> IO ()
sockaddr_free (SAPtr ptr) = foreign FFI_C "idrnet_free" (Ptr -> IO ()) ptr

||| Allocates an amount of memory given by the ByteLength parameter.
|||
||| Used to allocate a mutable pointer to be given to the Recv functions.
public
sock_alloc : ByteLength -> IO BufPtr
sock_alloc bl = map BPtr $ foreign FFI_C "idrnet_malloc" (Int -> IO Ptr) bl

||| The metadata about a socket
record Socket where
  constructor MkSocket
  descriptor : SocketDescriptor
  family : SocketFamily
  socketType : SocketType
  protocalNumber : ProtocolNumber

||| Creates a UNIX socket with the given family, socket type and protocol
||| number. Returns either a socket or an error.
socket : SocketFamily -> SocketType -> ProtocolNumber -> IO (Either SocketError Socket)
socket sf st pn = do
  socket_res <- foreign FFI_C "socket" (Int -> Int -> Int -> IO Int) (toCode sf) (toCode st) pn
  if socket_res == -1 then -- error
    map Left getErrno
  else
    return $ Right (MkSocket socket_res sf st pn)

||| Close a socket
close : Socket -> IO ()
close sock = foreign FFI_C "close" (Int -> IO ()) (descriptor sock)

private
saString : (Maybe SocketAddress) -> String
saString (Just sa) = show sa
saString Nothing = ""

||| Binds a socket to the given socket address and port.
||| Returns 0 on success, an error code otherwise.
bind : Socket -> (Maybe SocketAddress) -> Port -> IO Int
bind sock addr port = do
  bind_res <- foreign FFI_C "idrnet_bind" 
                  (Int -> Int -> Int -> String -> Int -> IO Int)
                  (descriptor sock) (toCode $ family sock) 
                  (toCode $ socketType sock) (saString addr) port
  if bind_res == (-1) then -- error
    getErrno
  else return 0 -- Success

||| Connects to a given address and port.
||| Returns 0 on success, and an error number on error.
connect : Socket -> SocketAddress -> Port -> IO Int
connect sock addr port = do
  conn_res <- foreign FFI_C "idrnet_connect"
                  (Int -> Int -> Int -> String -> Int -> IO Int)
                  (descriptor sock) (toCode $ family sock) (toCode $ socketType sock) (show addr) port
  if conn_res == (-1) then
    getErrno
  else return 0

||| Listens on a bound socket.
listen : Socket -> IO Int
listen sock = do
  listen_res <- foreign FFI_C "listen" (Int -> Int -> IO Int)
                    (descriptor sock) BACKLOG
  if listen_res == (-1) then
    getErrno
  else return 0

||| Parses a textual representation of an IPv4 address into a SocketAddress
parseIPv4 : String -> SocketAddress
parseIPv4 str = case splitted of
                  (i1 :: i2 :: i3 :: i4 :: _) => IPv4Addr i1 i2 i3 i4
                  _ => InvalidAddress
  where toInt' : String -> Integer
        toInt' = cast
        toInt : String -> Int
        toInt s = fromInteger $ toInt' s
        splitted : List Int
        splitted = map toInt (Prelude.Strings.split (\c => c == '.') str)


||| Retrieves a socket address from a sockaddr pointer
getSockAddr : SockaddrPtr -> IO SocketAddress
getSockAddr (SAPtr ptr) = do
  addr_family_int <- foreign FFI_C "idrnet_sockaddr_family" (Ptr -> IO Int) ptr
 -- putStrLn $ "Addr family int: " ++ (show addr_family_int)
  -- ASSUMPTION: Foreign call returns a valid int
  assert_total (case getSocketFamily addr_family_int of
    Just AF_INET => do
      ipv4_addr <- foreign FFI_C "idrnet_sockaddr_ipv4" (Ptr -> IO String) ptr
      return $ parseIPv4 ipv4_addr
    Just AF_INET6 => return IPv6Addr
    Just AF_UNSPEC => return InvalidAddress)

accept : Socket -> IO (Either SocketError (Socket, SocketAddress))
accept sock = do
  -- We need a pointer to a sockaddr structure. This is then passed into
  -- idrnet_accept and populated. We can then query it for the SocketAddr and free it.
  sockaddr_ptr <- foreign FFI_C "idrnet_create_sockaddr" (IO Ptr)
  accept_res <- foreign FFI_C "idrnet_accept" (Int -> Ptr -> IO Int) (descriptor sock) sockaddr_ptr
  if accept_res == (-1) then
    map Left getErrno
  else do
    let (MkSocket _ fam ty p_num) = sock
    sockaddr <- getSockAddr (SAPtr sockaddr_ptr)
    sockaddr_free (SAPtr sockaddr_ptr)
    return $ Right ((MkSocket accept_res fam ty p_num), sockaddr)

send : Socket -> String -> IO (Either SocketError ByteLength)
send sock dat = do
  send_res <- foreign FFI_C "idrnet_send" (Int -> String -> IO Int) (descriptor sock) dat
  if send_res == (-1) then
    map Left getErrno
  else
    return $ Right send_res


freeRecvStruct : RecvStructPtr -> IO ()
freeRecvStruct (RSPtr p) = foreign FFI_C "idrnet_free_recv_struct" (Ptr -> IO ()) p

freeRecvfromStruct : RecvfromStructPtr -> IO ()
freeRecvfromStruct (RFPtr p) = foreign FFI_C "idrnet_free_recvfrom_struct" (Ptr -> IO ()) p

recv : Socket -> Int -> IO (Either SocketError (String, ByteLength))
recv sock len = do
  -- Firstly make the request, get some kind of recv structure which
  -- contains the result of the recv and possibly the retrieved payload
  recv_struct_ptr <- foreign FFI_C "idrnet_recv" (Int -> Int -> IO Ptr) (descriptor sock) len
  recv_res <- foreign FFI_C "idrnet_get_recv_res" (Ptr -> IO Int) recv_struct_ptr
  if recv_res == (-1) then do
    errno <- getErrno
    freeRecvStruct (RSPtr recv_struct_ptr)
    return $ Left errno
  else 
    if recv_res == 0 then do
       freeRecvStruct (RSPtr recv_struct_ptr)
       return $ Left 0
    else do
       payload <- foreign FFI_C "idrnet_get_recv_payload" (Ptr -> IO String) recv_struct_ptr
       freeRecvStruct (RSPtr recv_struct_ptr)
       return $ Right (payload, recv_res)


||| Sends the data in a given memory location
sendBuf : Socket -> BufPtr -> ByteLength -> IO (Either SocketError ByteLength)
sendBuf sock (BPtr ptr) len = do
  send_res <- foreign FFI_C "idrnet_send_buf" (Int -> Ptr -> Int -> IO Int) (descriptor sock) ptr len
  if send_res == (-1) then
    map Left getErrno
  else
    return $ Right send_res

recvBuf : Socket -> BufPtr -> ByteLength -> IO (Either SocketError ByteLength)
recvBuf sock (BPtr ptr) len = do
  recv_res <- foreign FFI_C "idrnet_recv_buf" (Int -> Ptr -> Int -> IO Int) (descriptor sock) ptr len
  if (recv_res == (-1)) then
    map Left getErrno
  else
    return $ Right recv_res

sendTo : Socket -> SocketAddress -> Port -> String -> IO (Either SocketError ByteLength)
sendTo sock addr p dat = do
  sendto_res <- foreign FFI_C "idrnet_sendto" 
                   (Int -> String -> String -> Int -> Int -> IO Int) 
                   (descriptor sock) dat (show addr) p (toCode $ family sock)
  if sendto_res == (-1) then
    map Left getErrno
  else
    return $ Right sendto_res


sendToBuf : Socket -> SocketAddress -> Port -> BufPtr -> ByteLength -> IO (Either SocketError ByteLength)
sendToBuf sock addr p (BPtr dat) len = do
  sendto_res <- foreign FFI_C "idrnet_sendto_buf" 
                   (Int -> Ptr -> Int -> String -> Int -> Int -> IO Int) 
                   (descriptor sock) dat len (show addr) p (toCode $ family sock)
  if sendto_res == (-1) then
    map Left getErrno
  else
    return $ Right sendto_res


foreignGetRecvfromPayload : RecvfromStructPtr -> IO String
foreignGetRecvfromPayload (RFPtr p) 
   = foreign FFI_C "idrnet_get_recvfrom_payload" (Ptr -> IO String) p

foreignGetRecvfromAddr : RecvfromStructPtr -> IO SocketAddress
foreignGetRecvfromAddr (RFPtr p) = do
  sockaddr_ptr <- map SAPtr $ foreign FFI_C "idrnet_get_recvfrom_sockaddr" (Ptr -> IO Ptr) p
  getSockAddr sockaddr_ptr


foreignGetRecvfromPort : RecvfromStructPtr -> IO Port
foreignGetRecvfromPort (RFPtr p) = do
  sockaddr_ptr <- foreign FFI_C "idrnet_get_recvfrom_sockaddr" (Ptr -> IO Ptr) p
  port <- foreign FFI_C "idrnet_sockaddr_ipv4_port" (Ptr -> IO Int) sockaddr_ptr
  return port

recvFrom : Socket -> ByteLength -> IO (Either SocketError (UDPAddrInfo, String, ByteLength))
recvFrom sock bl = do
  recv_ptr <- foreign FFI_C "idrnet_recvfrom" (Int -> Int -> IO Ptr) 
                (descriptor sock) bl
  let recv_ptr' = RFPtr recv_ptr
  if !(nullPtr recv_ptr) then
    map Left getErrno
  else do
    result <- foreign FFI_C "idrnet_get_recvfrom_res" (Ptr -> IO Int) recv_ptr
    if result == -1 then do
      freeRecvfromStruct recv_ptr'
      map Left getErrno
    else do
      payload <- foreignGetRecvfromPayload recv_ptr'
      port <- foreignGetRecvfromPort recv_ptr'
      addr <- foreignGetRecvfromAddr recv_ptr'
      freeRecvfromStruct recv_ptr'
      return $ Right (MkUDPAddrInfo addr port, payload, result)


recvFromBuf : Socket -> BufPtr -> ByteLength -> IO (Either SocketError (UDPAddrInfo, ByteLength))
recvFromBuf sock (BPtr ptr) bl = do
  recv_ptr <- foreign FFI_C "idrnet_recvfrom_buf" (Int -> Ptr -> Int -> IO Ptr) (descriptor sock) ptr bl
  let recv_ptr' = RFPtr recv_ptr
  if !(nullPtr recv_ptr) then
    map Left getErrno
  else do
    result <- foreign FFI_C "idrnet_get_recvfrom_res" (Ptr -> IO Int) recv_ptr
    if result == -1 then do
      freeRecvfromStruct recv_ptr'
      map Left getErrno
    else do
      port <- foreignGetRecvfromPort recv_ptr'
      addr <- foreignGetRecvfromAddr recv_ptr'
      freeRecvfromStruct recv_ptr'
      return $ Right (MkUDPAddrInfo addr port, result + 1)


