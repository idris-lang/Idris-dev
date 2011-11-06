module Idris.Imports where

import Idris.AbsSyntax

import Core.TT
import Paths_idris

import System.FilePath
import System.Directory
import Control.Monad.State

data IFileType = IDR FilePath | IBC FilePath
    deriving Eq

srcPath :: FilePath -> FilePath
srcPath fp = let (n, ext) = splitExtension fp in
                 case ext of
                    "" -> fp ++ ".idr"
                    _ -> fp

-- Get name of byte compiled version of an import
ibcPath :: FilePath -> FilePath
ibcPath fp = let (n, ext) = splitExtension fp in
                 n ++ ".ibc"

findImport :: [FilePath] -> FilePath -> IO IFileType
findImport []     fp = fail $ "Can't find import " ++ fp
findImport (d:ds) fp = do let ibcp = ibcPath (d ++ "/" ++ fp)
                          let idrp = srcPath (d ++ "/" ++ fp)
                          ibc <- doesFileExist (ibcPath ibcp)
                          idr <- doesFileExist (srcPath idrp)
                          if ibc 
                             then return (IBC ibcp)
                             else if idr 
                                     then return (IDR idrp)
                                     else findImport ds fp


