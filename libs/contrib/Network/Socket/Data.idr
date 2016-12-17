||| Low-Level C Sockets bindings for Idris. Used by higher-level, cleverer things.
||| Types used by Network.Socket.Raw and Network.Socket.
|||
||| Original (C) SimonJF, MIT Licensed, 2014
||| Modified (C) The Idris Community, 2015, 2016
module Network.Socket.Data

%access public export

-- ------------------------------------------------------------ [ Type Aliases ]

ByteLength : Type
ByteLength = Int

ResultCode : Type
ResultCode = Int

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

Port : Type
Port = Int

-- --------------------------------------------------------------- [ Constants ]

||| Backlog used within listen() call -- number of incoming calls
BACKLOG : Int
BACKLOG = 20

EAGAIN : Int
EAGAIN =
  -- I'm sorry
  -- maybe
  unsafePerformIO $ foreign FFI_C "idrnet_geteagain" (() -> IO Int) ()

-- -------------------------------------------------------------- [ Interfaces ]

interface ToCode a where
  toCode : a -> Int

-- --------------------------------------------------------- [ Socket Families ]

||| Socket Families
|||
||| The ones that people might actually use. We're not going to need US
||| Government proprietary ones.
data SocketFamily : Type where
  ||| Unspecified
  AF_UNSPEC : SocketFamily

  ||| IP / UDP etc. IPv4
  AF_INET : SocketFamily

  |||  IP / UDP etc. IPv6
  AF_INET6 : SocketFamily

Show SocketFamily where
  show AF_UNSPEC = "AF_UNSPEC"
  show AF_INET   = "AF_INET"
  show AF_INET6  = "AF_INET6"

ToCode SocketFamily where
  toCode AF_UNSPEC = 0
  toCode AF_INET   = 2
  toCode AF_INET6  = 10

getSocketFamily : Int -> Maybe SocketFamily
getSocketFamily i =
    Prelude.List.lookup i [ (0, AF_UNSPEC)
                          , (2, AF_INET)
                          , (10, AF_INET6)
                          ]

-- ------------------------------------------------------------ [ Socket Types ]

||| Socket Types.
data SocketType : Type where
  ||| Not a socket, used in certain operations
  NotASocket : SocketType

  ||| TCP
  Stream : SocketType

  ||| UDP
  Datagram : SocketType

  ||| Raw sockets
  RawSocket : SocketType

Show SocketType where
  show NotASocket = "Not a socket"
  show Stream     = "Stream"
  show Datagram   = "Datagram"
  show RawSocket  = "Raw"

ToCode SocketType where
  toCode NotASocket = 0
  toCode Stream     = 1
  toCode Datagram   = 2
  toCode RawSocket  = 3

-- --------------------------------------------------------------- [ Addresses ]

||| Network Addresses
data SocketAddress : Type where
  IPv4Addr : Int -> Int -> Int -> Int -> SocketAddress

  ||| Not implemented (yet)
  IPv6Addr : SocketAddress

  Hostname : String -> SocketAddress

  ||| Used when there's a parse error
  InvalidAddress : SocketAddress

Show SocketAddress where
  show (IPv4Addr i1 i2 i3 i4) = concat $ Prelude.List.intersperse "." (map show [i1, i2, i3, i4])
  show IPv6Addr               = "NOT IMPLEMENTED YET"
  show (Hostname host)        = host
  show InvalidAddress         = "Invalid"

||| Parses a textual representation of an IPv4 address into a SocketAddress
parseIPv4 : String -> SocketAddress
parseIPv4 str =
    case splitted of
      (i1 :: i2 :: i3 :: i4 :: _) => IPv4Addr i1 i2 i3 i4
      otherwise                   => InvalidAddress
  where
    toInt' : String -> Integer
    toInt' = cast

    toInt : String -> Int
    toInt s = fromInteger $ toInt' s

    splitted : List Int
    splitted = map toInt (Prelude.Strings.split (\c => c == '.') str)

-- --------------------------------------------------------- [ UDP Information ]

-- TODO: Expand to non-string payloads
record UDPRecvData where
  constructor MkUDPRecvData
  remote_addr : SocketAddress
  remote_port : Port
  recv_data   : String
  data_len    : Int

record UDPAddrInfo where
  constructor MkUDPAddrInfo
  remote_addr : SocketAddress
  remote_port : Port

-- ----------------------------------------------------------------- [ Sockets ]
||| The metadata about a socket
record Socket where
  constructor MkSocket
  descriptor     : SocketDescriptor
  family         : SocketFamily
  socketType     : SocketType
  protocolNumber : ProtocolNumber

