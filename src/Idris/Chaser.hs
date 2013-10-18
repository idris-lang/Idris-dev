module Idris.Chaser(buildTree, getModuleFiles, ModuleTree(..)) where

import Idris.Parser
import Idris.AbsSyntax
import Idris.Imports
import Idris.Unlit
import Idris.Error
import Idris.IBC

import System.FilePath
import System.Directory
import Data.Time.Clock
import Control.Monad.Trans
import Control.Monad.State
import Data.List

import Debug.Trace

data ModuleTree = MTree { mod_path :: IFileType,
                          mod_needsRecheck :: Bool,
                          mod_time :: UTCTime,
                          mod_deps :: [ModuleTree] }
  deriving Show

latest :: UTCTime -> [ModuleTree] -> UTCTime
latest tm [] = tm
latest tm (m : ms) = latest (max tm (mod_time m)) (ms ++ mod_deps m)

-- Given a module tree, return the list of files to be loaded. If any
-- module has a descendent which needs reloading, return its source, otherwise
-- return the IBC

getModuleFiles :: [ModuleTree] -> [IFileType]
getModuleFiles ts = nub $ execState (modList ts) [] where
   modList :: [ModuleTree] -> State [IFileType] ()
   modList [] = return ()
   modList (m : ms) = do modTree [] m; modList ms

   modTree path (MTree p rechk tm deps)
           = do let file = chkReload rechk p
                -- Needs rechecking if 'rechk' is true, or if any of the
                -- modification times in 'deps' are later than tm
                let depMod = latest tm deps
                let needsRechk = rechk || depMod > tm

                st <- get
                if needsRechk then put $ nub (getSrc file : updateToSrc path st)
                              else put $ nub (file : st)
--                 when (not (ibc p) || rechk) $
                mapM_ (modTree (getSrc p : path)) deps

   ibc (IBC _ _) = True
   ibc _ = False
 
   chkReload False p = p
   chkReload True (IBC fn src) = chkReload True src
   chkReload True p = p

   getSrc (IBC fn src) = getSrc src
   getSrc f = f

   updateToSrc path [] = []
   updateToSrc path (x : xs) = if getSrc x `elem` path
                                  then getSrc x : updateToSrc path xs
                                  else x : updateToSrc path xs

getIModTime (IBC i _) = getModificationTime i
getIModTime (IDR i) = getModificationTime i
getIModTime (LIDR i) = getModificationTime i

buildTree :: [FilePath] -> -- already guaranteed built
             FilePath -> Idris [ModuleTree]
buildTree built fp = idrisCatch (btree [] fp)
                        (\e -> do now <- runIO $ getCurrentTime
                                  return [MTree (IDR fp) True now []])
 where
  btree done f = 
    do i <- getIState
       let file = takeWhile (/= ' ') f
       iLOG $ "CHASING " ++ show file
       ibcsd <- valIBCSubDir i
       ids <- allImportDirs 
       fp <- runIO $ findImport ids ibcsd file
       mt <- runIO $ getIModTime fp
       if (file `elem` built) 
          then return [MTree fp False mt []]
          else if file `elem` done 
                  then return []
                  else mkChildren fp 

    where mkChildren (LIDR fn) = do ms <- children True fn (f:done)
                                    mt <- runIO $ getModificationTime fn
                                    return [MTree (LIDR fn) True mt ms]
          mkChildren (IDR fn) = do ms <- children False fn (f:done)
                                   mt <- runIO $ getModificationTime fn
                                   return [MTree (IDR fn) True mt ms]
          mkChildren (IBC fn src) 
              = do srcexist <- runIO $ doesFileExist (getSrcFile src)
                   ms <- if srcexist then
                               do [MTree _ _ _ ms'] <- mkChildren src
                                  return ms'
                             else return []
                   mt <- idrisCatch (runIO $ getModificationTime fn)
                                    (\c -> runIO $ getIModTime src)
                   ok <- checkIBCUpToDate fn src
                   return [MTree (IBC fn src) ok mt ms]

          getSrcFile (IBC _ src) = getSrcFile src
          getSrcFile (LIDR src) = src
          getSrcFile (IDR src) = src

          -- FIXME: It's also not up to date if anything it imports has
          -- been modified since its own ibc has.

          checkIBCUpToDate fn (LIDR src) = older fn src
          checkIBCUpToDate fn (IDR src) = older fn src

          older ibc src = do exist <- runIO $ doesFileExist src
                             if exist then do
                                 ibct <- runIO $ getModificationTime ibc
                                 srct <- runIO $ getModificationTime src
                                 return (srct > ibct) 
                               else return False

  children :: Bool -> FilePath -> [FilePath] -> Idris [ModuleTree]
  children lit f done = idrisCatch
    (do exist <- runIO $ doesFileExist f
        if exist then do
            file_in <- runIO $ readFile f
            file <- if lit then tclift $ unlit f file_in else return file_in
            (_, modules, _) <- parseImports f file
            ms <- mapM (btree done) modules 
            return (concat ms)
           else return []) -- IBC with no source available
    (\c -> return []) -- error, can't chase modules here
