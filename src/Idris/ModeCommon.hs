{-|
Module      : Idris.ModeCommon
Description : Common utilities used by all modes.
License     : BSD3
Maintainer  : The Idris Community.
-}
module Idris.ModeCommon where

import Idris.AbsSyntax
import Idris.Chaser
import Idris.Core.TT
import Idris.Delaborate
import Idris.Erasure
import Idris.Error
import Idris.IBC
import Idris.Imports
import Idris.Info
import Idris.Output
import Idris.Parser hiding (indent)
import IRTS.Exports

import Prelude hiding (id, (.), (<$>))

import Control.Category
import Control.DeepSeq
import Control.Monad
import Control.Monad.Trans.State.Strict (get)
import Data.List hiding (group)
import Data.Maybe
import Network.Socket (PortNumber)
import System.Directory

defaultPort :: PortNumber
defaultPort = fromIntegral 4294


loadInputs :: [FilePath] -> Maybe Int -> Idris [FilePath]
loadInputs inputs toline -- furthest line to read in input source files
  = idrisCatch
       (do ist <- getIState
           -- if we're in --check and not outputting anything, don't bother
           -- loading, as it gets really slow if there's lots of modules in
           -- a package (instead, reload all at the end to check for
           -- consistency only)
           opts <- getCmdLine

           let loadCode = case opt getOutput opts of
                               [] -> not (NoREPL `elem` opts)
                               _ -> True

           -- For each ifile list, check it and build ibcs in the same clean IState
           -- so that they don't interfere with each other when checking

           importlists <- getImports [] inputs

           logParser 1 (show (map (\(i,m) -> (i, map import_path m)) importlists))

           let ninputs = zip [1..] inputs
           ifiles <- mapWhileOK (\(num, input) ->
                do putIState ist
                   modTree <- buildTree
                                   (map snd (take (num-1) ninputs))
                                   importlists
                                   input
                   let ifiles = getModuleFiles modTree
                   logParser 1 ("MODULE TREE : " ++ show modTree)
                   logParser 1 ("RELOAD: " ++ show ifiles)
                   when (not (all ibc ifiles) || loadCode) $
                        tryLoad False IBC_Building (filter (not . ibc) ifiles)
                   -- return the files that need rechecking
                   return (input, ifiles))
                      ninputs
           inew <- getIState
           let tidata = idris_tyinfodata inew
           -- If it worked, load the whole thing from all the ibcs together
           case errSpan inew of
              Nothing ->
                do putIState $!! ist { idris_tyinfodata = tidata }
                   ibcfiles <- mapM findNewIBC (nub (concatMap snd ifiles))
--                    logLvl 0 $ "Loading from " ++ show ibcfiles
                   tryLoad True (IBC_REPL True) (mapMaybe id ibcfiles)
              _ -> return ()
           exports <- findExports

           case opt getOutput opts of
               [] -> performUsageAnalysis (getExpNames exports) -- interactive
               _  -> return []  -- batch, will be checked by the compiler

           return (map fst ifiles))
        (\e -> do i <- getIState
                  case e of
                    At f e' -> do setErrSpan f
                                  iWarn f $ pprintErr i e'
                    ProgramLineComment -> return () -- fail elsewhere
                    _ -> do setErrSpan emptyFC -- FIXME! Propagate it
                                               -- Issue #1576 on the issue tracker.
                                               -- https://github.com/idris-lang/Idris-dev/issues/1576
                            iWarn emptyFC $ pprintErr i e
                  return [])
   where -- load all files, stop if any fail
         tryLoad :: Bool -> IBCPhase -> [IFileType] -> Idris ()
         tryLoad keepstate phase [] = warnTotality >> return ()
         tryLoad keepstate phase (f : fs)
                 = do ist <- getIState
                      let maxline
                            = case toline of
                                Nothing -> Nothing
                                Just l -> case f of
                                            IDR fn -> if any (fmatch fn) inputs
                                                         then Just l
                                                         else Nothing
                                            LIDR fn -> if any (fmatch fn) inputs
                                                          then Just l
                                                          else Nothing
                                            _ -> Nothing
                      loadFromIFile True phase f maxline
                      inew <- getIState
                      -- FIXME: Save these in IBC to avoid this hack! Need to
                      -- preserve it all from source inputs
                      --
                      -- Issue #1577 on the issue tracker.
                      --     https://github.com/idris-lang/Idris-dev/issues/1577
                      let tidata = idris_tyinfodata inew
                      let patdefs = idris_patdefs inew
                      ok <- noErrors
                      if ok then
                            -- The $!! here prevents a space leak on reloading.
                            -- This isn't a solution - but it's a temporary stopgap.
                            -- See issue #2386
                            do when (not keepstate) $ putIState $!! ist
                               ist <- getIState
                               putIState $!! ist { idris_tyinfodata = tidata,
                                                   idris_patdefs = patdefs }
                               tryLoad keepstate phase fs
                          else warnTotality

         ibc (IBC _ _) = True
         ibc _ = False

         fmatch ('.':'/':xs) ys = fmatch xs ys
         fmatch xs ('.':'/':ys) = fmatch xs ys
         fmatch xs ys = xs == ys

         findNewIBC :: IFileType -> Idris (Maybe IFileType)
         findNewIBC i@(IBC _ _) = return (Just i)
         findNewIBC s@(IDR f) = do ist <- get
                                   ibcsd <- valIBCSubDir ist
                                   let ibc = ibcPathNoFallback ibcsd f
                                   ok <- runIO $ doesFileExist ibc
                                   if ok then return (Just (IBC ibc s))
                                         else return Nothing
         findNewIBC s@(LIDR f) = do ist <- get
                                    ibcsd <- valIBCSubDir ist
                                    let ibc = ibcPathNoFallback ibcsd f
                                    ok <- runIO $ doesFileExist ibc
                                    if ok then return (Just (IBC ibc s))
                                          else return Nothing

         -- Like mapM, but give up when there's an error
         mapWhileOK f [] = return []
         mapWhileOK f (x : xs) = do x' <- f x
                                    ok <- noErrors
                                    if ok then do xs' <- mapWhileOK f xs
                                                  return (x' : xs')
                                          else return [x']

banner = "     ____    __     _                                          \n" ++
         "    /  _/___/ /____(_)____                                     \n" ++
         "    / // __  / ___/ / ___/     Version " ++ getIdrisVersion ++ "\n" ++
         "  _/ // /_/ / /  / (__  )      http://www.idris-lang.org/      \n" ++
         " /___/\\__,_/_/  /_/____/       Type :? for help               \n" ++
         "\n" ++
         "Idris is free software with ABSOLUTELY NO WARRANTY.            \n" ++
         "For details type :warranty."

warranty = "\n"                                                                          ++
           "\t THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS ``AS IS'' AND ANY  \n" ++
           "\t EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE     \n" ++
           "\t IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR    \n" ++
           "\t PURPOSE ARE DISCLAIMED.  IN NO EVENT SHALL THE COPYRIGHT HOLDERS BE   \n" ++
           "\t LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR   \n" ++
           "\t CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF  \n" ++
           "\t SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR       \n" ++
           "\t BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, \n" ++
           "\t WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE  \n" ++
           "\t OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN\n" ++
           "\t IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.\n"
