module Idris.IdrisDoc (generateDocs, DocTarget (..), idrisDocUsage) where

import Idris.AbsSyntax (IState)

type Failable = Either String

-- ist: IState
-- t:   What do generate documentation for
-- ot:  Where to output documentation
-- trm: Trace mode?       (will generate documentation for referred modules)
generateDocs :: IState -> DocTarget -> FilePath -> Bool -> IO (Either String ())
generateDocs ist t ot trm = err "IdrisDoc has not been implemented yet..."

err :: String -> IO (Failable ())
err s = return $ Left s

-- Target to generate documentation for
-- Namespace ns: Generate documentation for the namespace identified by 'ns'
-- Dir d:        Generate documentation for all namespaces in the directory 'd'
data DocTarget = Namespace String | Dir FilePath

idrisDocUsage = "Usage:   :mkdoc [notrace] [ns | dir] [TARGET]\n\n" ++
                "notrace: Do not generate IdrisDoc for addtionally referred namespaces.\n" ++
                "ns:      TARGET is a loaded namespace. TARGET required.\n" ++
                "dir:     TARGET is a directory to search recursively for .idr files. TARGET required.\n" ++
                "TARGET:  What to generate IdrisDoc for. By default interpreted as a namespace.\n" ++
                "<none>:  Same as ':mkdoc dir .'"