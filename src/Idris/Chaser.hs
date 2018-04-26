{-|
Module      : Idris.Chaser
Description : Module chaser to determine cycles and import modules.

License     : BSD3
Maintainer  : The Idris Community.
-}
{-# LANGUAGE FlexibleContexts #-}

module Idris.Chaser(
    buildTree, getImports
  , getModuleFiles
  , ModuleTree(..)
  ) where

import Idris.AbsSyntax
import Idris.Core.TT
import Idris.Error
import Idris.Imports
import Idris.Parser
import Idris.Unlit

import Control.Monad.State
import Data.List
import qualified Data.Map as M
import qualified Data.Set as S
import Data.Time.Clock
import System.Directory
import Util.System (readSource)

data ModuleTree = MTree { mod_path :: IFileType,
                          mod_needsRecheck :: Bool,
                          mod_time :: UTCTime,
                          mod_deps :: [ModuleTree] }
  deriving Show

latest :: UTCTime -> [IFileType] -> [ModuleTree] -> UTCTime
latest tm done [] = tm
latest tm done (m : ms)
    | mod_path m `elem` done = latest tm done ms
    | otherwise = latest (max tm (mod_time m)) (mod_path m : done) ms

modName :: IFileType -> String
modName (IDR fp) = fp
modName (LIDR fp) = fp
modName (IBC fp src) = modName src

-- | Given a module tree, return the list of files to be loaded. If
-- any module has a descendent which needs reloading, return its
-- source, otherwise return the IBC
getModuleFiles :: [ModuleTree] -> [IFileType]
getModuleFiles ts
    = let (files, (rebuild, _)) = runState (modList ts) (S.empty, M.empty) in
          updateToSrc rebuild (reverse files)
 where
   -- Get the order of building modules. As we go we'll find things that
   -- need rebuilding, which we keep track of in the Set.
   -- The order of the list matters - things which get built first appear
   -- in the list first. We'll remove any repetition later.
   modList :: [ModuleTree] ->
              State (S.Set IFileType,
                     M.Map IFileType (Bool, [IFileType])) [IFileType]
   modList [] = return []
   modList (m : ms) = do (_, fs) <- modTree S.empty m
                         fs' <- modList ms
                         pure (fs ++ fs')

   modTree path m@(MTree p rechk tm deps)
       = do let file = chkReload rechk p
            (rebuild, res) <- get
            case M.lookup file res of
                 Just ms -> pure ms
                 Nothing -> do
                    toBuildsAll <- mapM (modTree (S.insert (getSrc p) path)) deps
                    let (rechkDep_in, toBuilds) = unzip toBuildsAll
                    let rechkDep = or rechkDep_in

                    (rebuild, res) <- get

                    -- Needs rechecking if 'rechk' is true, or if any of the
                    -- modification times in 'deps' are later than tm, or
                    -- if any dependency needed rechecking
                    let depMod = latest tm [] deps
                    let needsRechk = rechkDep || rechk || depMod > tm

                    -- Remove duplicates, but keep the last...
                    let rnub = reverse . nub . reverse

                    let ret = if needsRechk
                                 then (needsRechk, rnub (getSrc file : concat toBuilds))
                                 else (needsRechk, rnub (file : concat toBuilds))

                    -- Cache the result
                    put (if needsRechk
                            then S.union path rebuild
                            else rebuild, M.insert file ret res)
                    pure ret

   chkReload False p = p
   chkReload True (IBC fn src) = chkReload True src
   chkReload True p = p

   getSrc (IBC fn src) = getSrc src
   getSrc f = f

   updateToSrc rebuilds [] = []
   updateToSrc rebuilds (x : xs)
       = if getSrc x `S.member` rebuilds
            then getSrc x : updateToSrc rebuilds xs
            else x : updateToSrc rebuilds xs

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
                   -- Modification time is the later of the source/ibc modification time
                   smt <- lift $ idrisCatch (runIO $ getIModTime src)
                                    (\c -> runIO $ getModificationTime fn)
                   mt <- lift $ idrisCatch (do t <- runIO $ getModificationTime fn
                                               return (max smt t))
                                    (\c -> return smt)
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
