{-|
Module      : Util.Net
Description : Utilities for Network IO.
Copyright   :
License     : BSD3
Maintainer  : The Idris Community.
-}
module Util.Net (listenOnLocalhost, listenOnLocalhostAnyPort) where

import Control.Exception (bracketOnError)
import Network hiding (socketPort)
import Network.BSD (getProtocolNumber)
import Network.Socket hiding (sClose)

-- Copied from upstream impl of listenOn
-- bound to localhost interface instead of iNADDR_ANY
listenOnLocalhost :: PortNumber -> IO Socket
listenOnLocalhost port = do
    proto <- getProtocolNumber "tcp"
    localhost <- inet_addr "127.0.0.1"
    bracketOnError
      (socket AF_INET Stream proto)
      (close)
      (\sock -> do
          setSocketOption sock ReuseAddr 1
          bind sock (SockAddrInet port localhost)
          listen sock maxListenQueue
          return sock
      )

listenOnLocalhostAnyPort :: IO (Socket, PortNumber)
listenOnLocalhostAnyPort = do
    proto <- getProtocolNumber "tcp"
    localhost <- inet_addr "127.0.0.1"
    bracketOnError
      (socket AF_INET Stream proto)
      (close)
      (\sock -> do
          setSocketOption sock ReuseAddr 1
          bind sock (SockAddrInet aNY_PORT localhost)
          listen sock maxListenQueue
          port <- socketPort sock
          return (sock, port)
      )
