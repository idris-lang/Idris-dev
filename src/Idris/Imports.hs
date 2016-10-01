{-|
Module      : Idris.Imports
Description : Code to handle import declarations.
Copyright   :
License     : BSD3
Maintainer  : The Idris Community.
-}
module Idris.Imports(
    IFileType(..), findImport, findInPath, findPkgIndex
  , ibcPathNoFallback, installedPackages, pkgIndex
  ) where

import Idris.AbsSyntax
import Idris.Core.TT
import Idris.Error
import IRTS.System (getIdrisLibDir)

import Control.Applicative ((<$>))
import Control.Monad.State.Strict
import Data.List (isSuffixOf)
import System.Directory
import System.FilePath

data IFileType = IDR FilePath | LIDR FilePath | IBC FilePath IFileType
    deriving (Show, Eq)

-- | Get the index file name for a package name
pkgIndex :: String -> FilePath
pkgIndex s = "00" ++ s ++ "-idx.ibc"

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
                                     else ibcsd </> d_fp
                                 n = dropExtension n_fp
                             in d </> n <.> "ibc"

ibcPathWithFallback :: FilePath -> FilePath -> IO FilePath
ibcPathWithFallback ibcsd fp = do let ibcp = ibcPath ibcsd True fp
                                  ibc <- doesFileExist' ibcp
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
                                ibc <- runIO $ doesFileExist' ibcp
                                idr  <- runIO $ doesFileExist' idrp
                                lidr <- runIO $ doesFileExist' lidrp
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
                          e <- doesFileExist' p
                          if e then return p else findInPath ds fp

findPkgIndex :: String -> Idris FilePath
findPkgIndex p = do let idx = pkgIndex p
                    ids <- allImportDirs
                    runIO $ findInPath ids idx


installedPackages :: IO [String]
installedPackages = do
  idir <- getIdrisLibDir
  filterM (goodDir idir) =<< dirContents idir
  where
  allFilesInDir base fp = do
    let fullpath = base </> fp
    isDir <- doesDirectoryExist' fullpath
    if isDir
      then fmap concat (mapM (allFilesInDir fullpath) =<< dirContents fullpath)
      else return [fp]
  dirContents = fmap (filter (not . (`elem` [".", ".."]))) . getDirectoryContents
  goodDir idir d = any (".ibc" `isSuffixOf`) <$> allFilesInDir idir d


-- | Case sensitive file existence check for Mac OS X.
doesFileExist' :: FilePath -> IO Bool
doesFileExist' = caseSensitive doesFileExist

-- | Case sensitive directory existence check for Mac OS X.
doesDirectoryExist' :: FilePath -> IO Bool
doesDirectoryExist' = caseSensitive doesDirectoryExist

caseSensitive :: (FilePath -> IO Bool) -> FilePath -> IO Bool
caseSensitive existsCheck name =
  do exists <- existsCheck name
     if exists
        then do contents <- getDirectoryContents (takeDirectory name)
                return $ (takeFileName name) `elem` contents
        else return False
