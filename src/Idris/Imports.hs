module Idris.Imports where

import Idris.AbsSyntax
import Idris.Error

import Idris.Core.TT

import System.FilePath
import System.Directory
import Control.Monad.State.Strict

data IFileType = IDR FilePath | LIDR FilePath | IBC FilePath IFileType
    deriving (Show, Eq)

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
ibcPath :: FilePath -> Bool -> FilePath -> FilePath
ibcPath ibcsd use_ibcsd fp = let (d_fp, n_fp) = splitFileName fp
                                 d = if (not use_ibcsd) || ibcsd == ""
                                     then d_fp
                                     else d_fp </> ibcsd
                                 n = dropExtension n_fp
                             in d </> n <.> "ibc"

ibcPathWithFallback :: FilePath -> FilePath -> IO FilePath
ibcPathWithFallback ibcsd fp = do let ibcp = ibcPath ibcsd True fp
                                  ibc <- doesFileExist ibcp
                                  return (if ibc
                                          then ibcp
                                          else ibcPath ibcsd False fp)

ibcPathNoFallback :: FilePath -> FilePath -> FilePath
ibcPathNoFallback ibcsd fp = ibcPath ibcsd True fp

findImport :: [FilePath] -> FilePath -> FilePath -> Idris IFileType
findImport []     ibcsd fp = ierror . Msg $ "Can't find import " ++ fp
findImport (d:ds) ibcsd fp = do let fp_full = d </> fp
                                ibcp <- runIO $ ibcPathWithFallback ibcsd fp_full
                                let idrp = srcPath fp_full
                                let lidrp = lsrcPath fp_full
                                ibc <- runIO $ doesFileExist ibcp
                                idr  <- runIO $ doesFileExist idrp
                                lidr <- runIO $ doesFileExist lidrp
--                              when idr $ putStrLn $ idrp ++ " ok"
--                              when lidr $ putStrLn $ lidrp ++ " ok"
--                              when ibc $ putStrLn $ ibcp ++ " ok"
                                let isrc = if lidr
                                           then LIDR lidrp
                                           else IDR idrp
                                if ibc
                                  then return (IBC ibcp isrc)
                                  else if (idr || lidr)
                                       then return isrc
                                       else findImport ds ibcsd fp

-- find a specific filename somewhere in a path

findInPath :: [FilePath] -> FilePath -> IO FilePath
findInPath [] fp = fail $ "Can't find file " ++ fp
findInPath (d:ds) fp = do let p = d </> fp
                          e <- doesFileExist p
                          if e then return p else findInPath ds fp
