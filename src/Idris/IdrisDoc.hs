module Idris.IdrisDoc (generateDocs) where

import Idris.AbsSyntax (IState)

type Failable = Either String

-- ist: IState
-- nss: List of namespaces to generate documentation for
-- out: Where to place the directory of documentation
generateDocs :: IState -> [String] -> FilePath -> IO (Either String ())
generateDocs ist nss out = err "IdrisDoc is still in development..."

err :: String -> IO (Failable ())
err s = return $ Left s