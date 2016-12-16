||| Low-Level C Sockets bindings for Idris. Used by higher-level, cleverer things.
||| Type-unsafe parts. Use Network.Socket for a safe variant.
|||
||| Original (C) SimonJF, MIT Licensed, 2014
||| Modified (C) The Idris Community, 2015, 2016
module Network.Socket.Raw

import public Network.Socket.Types

%include C "idris_net.h"
%include C "sys/types.h"
%include C "sys/socket.h"
%include C "netdb.h"

-- ---------------------------------------------------------------- [ Pointers ]

public export
data RecvStructPtr = RSPtr Ptr
public export
data RecvfromStructPtr = RFPtr Ptr

public export
data BufPtr = BPtr Ptr

public export
data SockaddrPtr = SAPtr Ptr

-- ---------------------------------------------------------- [ Socket Utilies ]

||| Frees a given pointer
public export
sock_free : BufPtr -> IO ()
sock_free (BPtr ptr) = foreign FFI_C "idrnet_free" (Ptr -> IO ()) ptr

public export
sockaddr_free : SockaddrPtr -> IO ()
sockaddr_free (SAPtr ptr) = foreign FFI_C "idrnet_free" (Ptr -> IO ()) ptr

||| Allocates an amount of memory given by the ByteLength parameter.
|||
||| Used to allocate a mutable pointer to be given to the Recv functions.
public export
sock_alloc : ByteLength -> IO BufPtr
sock_alloc bl = map BPtr $ foreign FFI_C "idrnet_malloc" (Int -> IO Ptr) bl

