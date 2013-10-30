module Util.Net (listenOnLocalhost) where

import Network
import Network.Socket hiding (sClose, PortNumber)
import Network.BSD (getProtocolNumber)
import Control.Exception (bracketOnError)

-- Copied from upstream impl of listenOn
-- bound to localhost interface instead of iNADDR_ANY
listenOnLocalhost (PortNumber port) = do
    proto <- getProtocolNumber "tcp"
    localhost <- inet_addr "127.0.0.1"
    bracketOnError
      (socket AF_INET Stream proto)
      (sClose)
      (\sock -> do
          setSocketOption sock ReuseAddr 1
          bindSocket sock (SockAddrInet port localhost)
          listen sock maxListenQueue
          return sock
      )

