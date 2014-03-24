module Idris.IdrisDoc (generateDocs, DocTarget) where

import Idris.AbsSyntax (IState)
import Idris.Core.TT (Err')

type Failable = Either String

-- ist: IState
-- t:   What do generate documentation for
-- ot:  Where to output documentation
-- trm: Trace mode?       (will generate documentation for referred modules)
generateDocs :: IState -> DocTarget -> Filepath -> Bool -> IO (Either String ())
generateDocs ist t ot trm = error "IdrisDoc has not been implemented yet..."

error :: String -> IO (Failable ())
error s = return Left s

-- Target to generate documentation for
-- Namespace ns: Generate documentation for the namespace identified by 'ns'
-- Dir d:        Generate documentation for all namespaces in the directory 'd'
data DocTarget = Namespace String | Dir FilePath