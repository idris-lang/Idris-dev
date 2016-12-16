||| Low-Level C Sockets bindings for Idris. Used by higher-level, cleverer things.
||| Types used by Network.Socket.Raw and Network.Socket.
|||
||| Original (C) SimonJF, MIT Licensed, 2014
||| Modified (C) The Idris Community, 2015, 2016
module Network.Socket.Types

-- ------------------------------------------------------------ [ Type Aliases ]

public export
ByteLength : Type
ByteLength = Int

public export
ResultCode : Type
ResultCode = Int

||| Protocol Number.
|||
||| Generally good enough to just set it to 0.
public export
ProtocolNumber : Type
ProtocolNumber = Int

||| SocketError: Error thrown by a socket operation
public export
SocketError : Type
SocketError = Int

||| SocketDescriptor: Native C Socket Descriptor
public export
SocketDescriptor : Type
SocketDescriptor = Int

public export
Port : Type
Port = Int

-- --------------------------------------------------------------- [ Constants ]

||| Backlog used within listen() call -- number of incoming calls
public export
BACKLOG : Int
BACKLOG = 20

-- FIXME: This *must* be pulled in from C
public export
EAGAIN : Int
EAGAIN = 11

-- -------------------------------------------------------------- [ Interfaces ]

public export
interface ToCode a where
  toCode : a -> Int

-- --------------------------------------------------------- [ Socket Families ]

||| Socket Families
|||
||| The ones that people might actually use. We're not going to need US
||| Government proprietary ones.
public export
data SocketFamily : Type where
  ||| Unspecified
  AF_UNSPEC : SocketFamily

  ||| IP / UDP etc. IPv4
  AF_INET : SocketFamily

  |||  IP / UDP etc. IPv6
  AF_INET6 : SocketFamily

public export
Show SocketFamily where
  show AF_UNSPEC = "AF_UNSPEC"
  show AF_INET   = "AF_INET"
  show AF_INET6  = "AF_INET6"

public export
ToCode SocketFamily where
  toCode AF_UNSPEC = 0
  toCode AF_INET   = 2
  toCode AF_INET6  = 10

public export
getSocketFamily : Int -> Maybe SocketFamily
getSocketFamily i =
    Prelude.List.lookup i [ (0, AF_UNSPEC)
                          , (2, AF_INET)
                          , (10, AF_INET6)
                          ]

-- ------------------------------------------------------------ [ Socket Types ]

||| Socket Types.
public export
data SocketType : Type where
  ||| Not a socket, used in certain operations
  NotASocket : SocketType

  ||| TCP
  Stream : SocketType

  ||| UDP
  Datagram : SocketType

  ||| Raw sockets
  RawSocket : SocketType

public export
Show SocketType where
  show NotASocket = "Not a socket"
  show Stream     = "Stream"
  show Datagram   = "Datagram"
  show RawSocket  = "Raw"

public export
ToCode SocketType where
  toCode NotASocket = 0
  toCode Stream     = 1
  toCode Datagram   = 2
  toCode RawSocket  = 3

-- --------------------------------------------------------------- [ Addresses ]

||| Network Addresses
public export
data SocketAddress : Type where
  IPv4Addr : Int -> Int -> Int -> Int -> SocketAddress

  ||| Not implemented (yet)
  IPv6Addr : SocketAddress

  Hostname : String -> SocketAddress

  ||| Used when there's a parse error
  InvalidAddress : SocketAddress

public export
Show SocketAddress where
  show (IPv4Addr i1 i2 i3 i4) = concat $ Prelude.List.intersperse "." (map show [i1, i2, i3, i4])
  show IPv6Addr               = "NOT IMPLEMENTED YET"
  show (Hostname host)        = host
  show InvalidAddress         = "Invalid"

-- --------------------------------------------------------- [ UDP Information ]

-- TODO: Expand to non-string payloads
public export
record UDPRecvData where
  constructor MkUDPRecvData
  remote_addr : SocketAddress
  remote_port : Port
  recv_data   : String
  data_len    : Int

public export
record UDPAddrInfo where
  constructor MkUDPAddrInfo
  remote_addr : SocketAddress
  remote_port : Port

-- ----------------------------------------------------------------- [ Sockets ]
||| The metadata about a socket
public export
record Socket where
  constructor MkSocket
  descriptor     : SocketDescriptor
  family         : SocketFamily
  socketType     : SocketType
  protocolNumber : ProtocolNumber

