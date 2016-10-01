{-|
Module      : Idris.Chaser
Description : Module chaser to determine cycles and import modules.
Copyright   :
License     : BSD3
Maintainer  : The Idris Community.
-}
module Idris.Chaser(
    buildTree, getImports
  , getModuleFiles
  , ModuleTree(..)
  ) where

import Idris.AbsSyntax
import Idris.Core.TT
import Idris.Error
import Idris.IBC
import Idris.Imports
import Idris.Parser
import Idris.Unlit

import Control.Monad.State
import Control.Monad.Trans
import Data.List
import Data.Time.Clock
import Debug.Trace
import System.Directory
import System.FilePath
import Util.System (readSource, writeSource)

data ModuleTree = MTree { mod_path :: IFileType,
                          mod_needsRecheck :: Bool,
                          mod_time :: UTCTime,
                          mod_deps :: [ModuleTree] }
  deriving Show

latest :: UTCTime -> [ModuleTree] -> UTCTime
latest tm [] = tm
latest tm (m : ms) = latest (max tm (mod_time m)) (ms ++ mod_deps m)

-- | Given a module tree, return the list of files to be loaded. If
-- any module has a descendent which needs reloading, return its
-- source, otherwise return the IBC
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

-- | Strip quotes and the backslash escapes that Haskeline adds
extractFileName :: String -> String
extractFileName ('"':xs) = takeWhile (/= '"') xs
extractFileName ('\'':xs) = takeWhile (/= '\'') xs
extractFileName x = build x []
                        where
                            build [] acc = reverse $ dropWhile (== ' ') acc
                            build ('\\':' ':xs) acc = build xs (' ':acc)
                            build (x:xs) acc = build xs (x:acc)

getIModTime (IBC i _) = getModificationTime i
getIModTime (IDR i) = getModificationTime i
getIModTime (LIDR i) = getModificationTime i

getImports :: [(FilePath, [ImportInfo])]
           -> [FilePath]
           -> Idris [(FilePath, [ImportInfo])]
getImports acc [] = return acc
getImports acc (f : fs) = do
   i <- getIState
   let file = extractFileName f
   ibcsd <- valIBCSubDir i
   idrisCatch (do
       srcds <- allSourceDirs
       fp <- findImport srcds ibcsd file
       let parsef = fname fp
       case lookup parsef acc of
            Just _ -> getImports acc fs
            _ -> do
               exist <- runIO $ doesFileExist parsef
               if exist then do
                   src_in <- runIO $ readSource parsef
                   src <- if lit fp then tclift $ unlit parsef src_in
                                    else return src_in
                   (_, _, modules, _) <- parseImports parsef src
                   clearParserWarnings
                   getImports ((parsef, modules) : acc)
                              (fs ++ map import_path modules)
                     else getImports ((parsef, []) : acc) fs)
        (\_ -> getImports acc fs) -- not in current soure tree, ignore
  where
    lit (LIDR _) = True
    lit _ = False

    fname (IDR fn) = fn
    fname (LIDR fn) = fn
    fname (IBC _ src) = fname src

buildTree :: [FilePath]                 -- ^ already guaranteed built
          -> [(FilePath, [ImportInfo])] -- ^ import lists (don't reparse)
          -> FilePath
          -> Idris [ModuleTree]
buildTree built importlists fp = evalStateT (btree [] fp) []
 where
  addFile :: FilePath -> [ModuleTree] ->
             StateT [(FilePath, [ModuleTree])] Idris [ModuleTree]
  addFile f m = do fs <- get
                   put ((f, m) : fs)
                   return m

  btree :: [FilePath] -> FilePath ->
           StateT [(FilePath, [ModuleTree])] Idris [ModuleTree]
  btree stk f =
    do i <- lift getIState
       let file = extractFileName f
       lift $ logLvl 1 $ "CHASING " ++ show file ++ " (" ++ show fp ++ ")"
       ibcsd <- lift $ valIBCSubDir i
       ids   <- lift allImportDirs
       fp   <- lift $ findImport ids ibcsd file
       lift $ logLvl 1 $ "Found " ++ show fp
       mt <- lift $ runIO $ getIModTime fp
       if (file `elem` built)
          then return [MTree fp False mt []]
               else if file `elem` stk then
                       do lift $ tclift $ tfail
                            (Msg $ "Cycle detected in imports: "
                                     ++ showSep " -> " (reverse (file : stk)))
                 else do donetree <- get
                         case lookup file donetree of
                            Just t -> return t
                            _ -> do ms <- mkChildren file fp
                                    addFile file ms

    where mkChildren file (LIDR fn) = do ms <- children True fn (file : stk)
                                         mt <- lift $ runIO $ getModificationTime fn
                                         return [MTree (LIDR fn) True mt ms]
          mkChildren file (IDR fn) = do ms <- children False fn (file : stk)
                                        mt <- lift $ runIO $ getModificationTime fn
                                        return [MTree (IDR fn) True mt ms]
          mkChildren file (IBC fn src)
              = do srcexist <- lift $ runIO $ doesFileExist (getSrcFile src)
                   ms <- if srcexist then
                               do [MTree _ _ _ ms'] <- mkChildren file src
                                  return ms'
                             else return []
                   mt <- lift $ idrisCatch (runIO $ getModificationTime fn)
                                    (\c -> runIO $ getIModTime src)
                   -- FIXME: It's also not up to date if anything it imports has
                   -- been modified since its own ibc has.
                   --
                   -- Issue #1592 on the issue tracker.
                   --
                   -- https://github.com/idris-lang/Idris-dev/issues/1592
                   ibcOutdated <- lift $ fn `younger` (getSrcFile src)
                   -- FIXME (EB): The below 'hasValidIBCVersion' that's
                   -- commented out appears to be breaking reloading in vim
                   -- mode. Until we know why, I've commented it out.
                   ibcValid <- return True -- hasValidIBCVersion fn
                   return [MTree (IBC fn src) (ibcOutdated || not ibcValid) mt ms]

          getSrcFile (IBC _ src) = getSrcFile src
          getSrcFile (LIDR src) = src
          getSrcFile (IDR src) = src

          younger ibc src = do exist <- runIO $ doesFileExist src
                               if exist then do
                                   ibct <- runIO $ getModificationTime ibc
                                   srct <- runIO $ getModificationTime src
                                   return (srct > ibct)
                                 else return False

  children :: Bool -> FilePath -> [FilePath] ->
              StateT [(FilePath, [ModuleTree])] Idris [ModuleTree]
  children lit f stk = -- idrisCatch
     do exist <- lift $ runIO $ doesFileExist f
        if exist then do
            lift $ logLvl 1 $ "Reading source " ++ show f
            let modules = maybe [] id (lookup f importlists)
            ms <- mapM (btree stk . import_path) modules
            return (concat ms)
           else return [] -- IBC with no source available
--     (\c -> return []) -- error, can't chase modules here
