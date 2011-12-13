module Idris.Imports where

import Idris.AbsSyntax

import Core.TT
import Paths_idris

import System.FilePath
import System.Directory
import Control.Monad.State

data IFileType = IDR FilePath | LIDR FilePath | IBC FilePath IFileType 
    deriving Eq

srcPath :: FilePath -> FilePath
srcPath fp = let (n, ext) = splitExtension fp in
                 case ext of
                    ".idr" -> fp
                    _ -> fp ++ ".idr"

lsrcPath :: FilePath -> FilePath
lsrcPath fp = let (n, ext) = splitExtension fp in
                  case ext of
                     ".lidr" -> fp
                     _ -> fp ++ ".lidr"

-- Get name of byte compiled version of an import
ibcPath :: FilePath -> FilePath
ibcPath fp = let (n, ext) = splitExtension fp in
                 n ++ ".ibc"

findImport :: [FilePath] -> FilePath -> IO IFileType
findImport []     fp = fail $ "Can't find import " ++ fp
findImport (d:ds) fp = do let ibcp = ibcPath (d ++ "/" ++ fp)
                          let idrp = srcPath (d ++ "/" ++ fp)
                          let lidrp = lsrcPath (d ++ "/" ++ fp)
                          ibc  <- doesFileExist ibcp
                          idr  <- doesFileExist idrp
                          lidr <- doesFileExist lidrp
--                           when idr $ putStrLn $ idrp ++ " ok"
--                           when lidr $ putStrLn $ lidrp ++ " ok"
--                           when ibc $ putStrLn $ ibcp ++ " ok"
                          let isrc = if lidr then LIDR lidrp
                                             else IDR idrp
                          if ibc 
                             then return (IBC ibcp isrc)
                             else if (idr || lidr) 
                                     then return isrc
                                     else findImport ds fp

-- find a specific filename somewhere in a path

findInPath :: [FilePath] -> FilePath -> IO FilePath
findInPath [] fp = fail $ "Can't find file " ++ fp
findInPath (d:ds) fp = do let p = d ++ "/" ++ fp
                          e <- doesFileExist p
                          if e then return p else findInPath ds p


