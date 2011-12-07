module Idris.Imports where

import Idris.AbsSyntax

import Core.TT
import Paths_idris

import System.FilePath
import System.Directory
import Control.Monad.State

data IFileType = IDR FilePath | IBC FilePath FilePath
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
                             then return (IBC ibcp idrp)
                             else if idr 
                                     then return (IDR idrp)
                                     else findImport ds fp

-- find a specific filename somewhere in a path

findInPath :: [FilePath] -> FilePath -> IO FilePath
findInPath [] fp = fail $ "Can't find file " ++ fp
findInPath (d:ds) fp = do let p = d ++ "/" ++ fp
                          e <- doesFileExist p
                          if e then return p else findInPath ds p


