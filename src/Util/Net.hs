{-|
Module      : Util.Net
Description : Utilities for Network IO.

License     : BSD3
Maintainer  : The Idris Community.
-}
module Util.Net (listenOnLocalhost, listenOnLocalhostAnyPort) where

import Control.Exception (bracketOnError)
import Network.Socket
-- Copied from upstream impl of listenOn
-- bound to localhost interface instead of iNADDR_ANY
listenOnLocalhost :: PortNumber -> IO Socket
listenOnLocalhost port = do
    let hints = defaultHints { addrSocketType = Stream }
    localhost:_ <- getAddrInfo (Just hints) (Just "127.0.0.1") (Just $ show port)
    bracketOnError
      (socket AF_INET Stream defaultProtocol)
      (close)
      (\sock -> do
          setSocketOption sock ReuseAddr 1
          bind sock (addrAddress localhost)
          listen sock maxListenQueue
          return sock
      )

listenOnLocalhostAnyPort :: IO (Socket, PortNumber)
listenOnLocalhostAnyPort = do
    let hints = defaultHints { addrSocketType = Stream }
    localhost:_ <- getAddrInfo (Just hints) (Just "127.0.0.1") (Just "0")
    bracketOnError
      (socket AF_INET Stream defaultProtocol)
      (close)
      (\sock -> do
          setSocketOption sock ReuseAddr 1
          bind sock (addrAddress localhost)
          listen sock maxListenQueue
          port <- socketPort sock
          return (sock, port)
      )
