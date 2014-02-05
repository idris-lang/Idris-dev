-- Time to do this properly.
-- Low-Level C Sockets bindings for Idris. Used by higher-level, cleverer things.
-- (C) SimonJF, MIT Licensed, 2014
module Network.Socket

%include C "idris_net.h"
%include C "sys/types.h" -- Pushing my luck, might need to re-export everything
%include C "sys/socket.h" 
%include C "netdb.h"

%access public

ByteLength : Type
ByteLength = Int

class ToCode a where
  toCode : a -> Int

-- Socket Families.
-- The ones that people might actually use. We're not going to need US Government
-- proprietary ones...
data SocketFamily = AF_UNSPEC -- Unspecified
                  | AF_INET   -- IP / UDP etc. IPv4
                  | AF_INET6  -- IP / UDP etc. IPv6

instance Show SocketFamily where
  show AF_UNSPEC = "AF_UNSPEC"
  show AF_INET   = "AF_INET"
  show AF_INET6  = "AF_INET4"

instance ToCode SocketFamily where
  toCode AF_UNSPEC = 0
  toCode AF_INET   = 2
  toCode AF_INET6  = 10

getSocketFamily : Int -> Maybe SocketFamily
getSocketFamily i = Prelude.List.lookup i [(0, AF_UNSPEC), (2, AF_INET), (10, AF_INET6)]

-- Socket Types.
data SocketType = NotASocket  -- Not a socket, used in certain operations
                | Stream      -- TCP
                | Datagram    -- UDP
                | RawSocket   -- Raw sockets. A guy can dream.

instance Show SocketType where
  show NotASocket = "Not a socket"
  show Stream     = "Stream"
  show Datagram   = "Datagram"
  show Raw        = "Raw"

instance ToCode SocketType where
  toCode NotASocket = 0
  toCode Stream     = 1
  toCode Datagram   = 2
  toCode Raw        = 3

-- Protocol Number. Generally good enough to just set it to 0.
ProtocolNumber : Type
ProtocolNumber = Int

-- SocketError: Error thrown by a socket operation
SocketError : Type
SocketError = Int

-- SocketDescriptor: Native C Socket Descriptor
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

-- Backlog used within listen() call -- number of incoming calls
BACKLOG : Int
BACKLOG = 20

-- FIXME: This *must* be pulled in from C
EAGAIN : Int 
EAGAIN = 11

-- Allocates an amount of memory given by the ByteLength parameter.
-- Used to allocate a mutable pointer to be given to the Recv functions.
private
alloc : ByteLength -> IO Ptr
alloc bl = mkForeign (FFun "idrnet_malloc" [FInt] FPtr) bl

-- Frees a given pointer
private
free : Ptr -> IO ()
free ptr = mkForeign (FFun "idrnet_free" [FPtr] FUnit) ptr

record Socket : Type where
  MkSocket : (descriptor : SocketDescriptor) ->
             (family : SocketFamily) ->
             (socketType : SocketType) ->
             (protocolNumber : ProtocolNumber) ->
             Socket

getErrno : IO Int
getErrno = mkForeign (FFun "idrnet_errno" [] FInt)

-- Creates a UNIX socket with the given family, socket type and protocol number.
-- Returns either a socket or an error.
socket : SocketFamily -> SocketType -> ProtocolNumber -> IO (Either SocketError Socket)
socket sf st pn = do
  socket_res <- mkForeign (FFun "socket" [FInt, FInt, FInt] FInt) (toCode sf) (toCode st) pn
  if socket_res == -1 then -- error
    map Left getErrno
  else 
    return $ Right (MkSocket socket_res sf st pn)


close : Socket -> IO ()
close sock = mkForeign (FFun "close" [FInt] FUnit) (descriptor sock)

-- Binds a socket to the given socket address and port.
-- Returns 0 on success, an error code otherwise.
bind : Socket -> SocketAddress -> Port -> IO Int
bind sock addr port = do
  bind_res <- (mkForeign (FFun "idrnet_bind" [FInt, FInt, FInt, FString, FInt] FInt) 
                           (descriptor sock) (toCode $ family sock) (toCode $ socketType sock) (show addr) port)
  if bind_res == (-1) then -- error
    getErrno
  else return 0 -- Success

-- Connects to a given address and port.
-- Returns 0 on success, and an error number on error.
connect : Socket -> SocketAddress -> Port -> IO Int
connect sock addr port = do
  conn_res <- (mkForeign (FFun "idrnet_connect" [FInt, FInt, FInt, FString, FInt] FInt)
                           (descriptor sock) (toCode $ family sock) (toCode $ socketType sock) (show addr) port)
  if conn_res == (-1) then
    getErrno
  else return 0

-- Listens on a bound socket.
listen : Socket -> IO Int
listen sock = do
  listen_res <- mkForeign (FFun "listen" [FInt, FInt] FInt) (descriptor sock) BACKLOG
  if listen_res == (-1) then
    getErrno
  else return 0

-- Parses a textual representation of an IPv4 address into a SocketAddress
private
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


-- Retrieves a socket address from a sockaddr pointer
private
getSockAddr : Ptr -> IO SocketAddress
getSockAddr ptr = do
  addr_family_int <- mkForeign (FFun "idrnet_sockaddr_family" [FPtr] FInt) ptr
  -- FIXME: Is this really a safe assertion? Depends where the Ptr came
  -- from!
  assert_total $ case getSocketFamily addr_family_int of
    Just AF_INET => do
      ipv4_addr <- mkForeign (FFun "idrnet_sockaddr_ipv4" [FPtr] FString) ptr
      return $ parseIPv4 ipv4_addr
    Just AF_INET6 => return IPv6Addr
    Just AF_UNSPEC => return IPv6Addr -- FIXME: Horrible hack

-- Accepts a connection from a listening socket.
accept : Socket -> IO (Either SocketError (Socket, SocketAddress))
accept sock = do
  -- We need a pointer to a sockaddr structure. This is then passed into
  -- idrnet_accept and populated. We can then query it for the SocketAddr and free it.
  sockaddr_ptr <- mkForeign (FFun "idrnet_create_sockaddr" [] FPtr) 
  accept_res <- mkForeign (FFun "idrnet_accept" [FInt, FPtr] FInt) (descriptor sock) sockaddr_ptr
  if accept_res == (-1) then
    map Left getErrno
  else do
    let (MkSocket _ fam ty p_num) = sock
    sockaddr <- getSockAddr sockaddr_ptr
    free sockaddr_ptr
    return $ Right ((MkSocket accept_res fam ty p_num), sockaddr)

send : Socket -> String -> IO (Either SocketError ByteLength)
send sock dat = do
  send_res <- mkForeign (FFun "idrnet_send" [FInt, FString] FInt) (descriptor sock) dat
  if send_res == (-1) then
    map Left getErrno
  else
    return $ Right send_res

private
freeRecvStruct : Ptr -> IO ()
freeRecvStruct p = mkForeign (FFun "idrnet_free_recv_struct" [FPtr] FUnit) p


recv : Socket -> Int -> IO (Either SocketError (String, ByteLength))
recv sock len = do
  -- Firstly make the request, get some kind of recv structure which
  -- contains the result of the recv and possibly the retrieved payload
  recv_struct_ptr <- mkForeign (FFun "idrnet_recv" [FInt, FInt] FPtr) (descriptor sock) len
  recv_res <- mkForeign (FFun "idrnet_get_recv_res" [FPtr] FInt) recv_struct_ptr
  if recv_res == (-1) then do
    errno <- getErrno
    freeRecvStruct recv_struct_ptr
    return $ Left errno
  else 
    if recv_res == 0 then do
       freeRecvStruct recv_struct_ptr
       return $ Left 0
    else do
       payload <- mkForeign (FFun "idrnet_get_recv_payload" [FPtr] FString) recv_struct_ptr
       freeRecvStruct recv_struct_ptr
       return $ Right (payload, recv_res)


-- Sends the data in a given memory location
sendBuf : Socket -> Ptr -> ByteLength -> IO (Either SocketError ByteLength)
sendBuf sock ptr len = do
  send_res <- mkForeign (FFun "idrnet_send_buf" [FInt, FPtr, FInt] FInt) (descriptor sock) ptr len
  if send_res == (-1) then
    map Left getErrno
  else 
    return $ Right send_res

recvBuf : Socket -> Ptr -> ByteLength -> IO (Either SocketError ByteLength)
recvBuf sock ptr len = do
  recv_res <- mkForeign (FFun "idrnet_recv_buf" [FInt, FPtr, FInt] FInt) (descriptor sock) ptr len
  if (recv_res == (-1)) then
    map Left getErrno
  else
    return $ Right recv_res

