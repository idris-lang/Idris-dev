module Main where

import Control.Monad (when)
import System.Exit (exitSuccess)

import Idris.AbsSyntax (runIO, Idris, setQuiet, setVerbose, Opt(..))
import Idris.REPL (idrisMain, runMain, runClient)
import Idris.Error
import Idris.CmdOptions (opt, runArgParser, getClient, getPort,
                         getPkg, getPkgCheck, getPkgClean, getPkgMkDoc, getPkgTest, getPkgREPL)
import Idris.Info
import Idris.Info.Show
import Idris.Package
import Util.System (setupBundledCC)

processShowOptions :: [Opt] -> Idris ()
processShowOptions opts = runIO $ do
  when (ShowAll `elem` opts)          $ showExitIdrisInfo
  when (ShowLoggingCats `elem` opts)  $ showExitIdrisLoggingCategories
  when (ShowIncs `elem` opts)         $ showExitIdrisFlagsInc
  when (ShowLibs `elem` opts)         $ showExitIdrisFlagsLibs
  when (ShowLibdir `elem` opts)       $ showExitIdrisLibDir
  when (ShowPkgs `elem` opts)         $ showExitIdrisInstalledPackages

processClientOptions :: [Opt] -> Idris ()
processClientOptions opts =
  case opt getClient opts of
     []    -> return ()
     (c:_) -> do setVerbose False
                 setQuiet True
                 runIO $ do
                   runClient (getPort opts) c
                   exitSuccess

processPackageOptions :: [Opt] -> Idris ()
processPackageOptions opts = do
  case opt getPkgCheck opts of
     [] -> return ()
     fs -> runIO $ do
             mapM_ (checkPkg opts (WarnOnly `elem` opts) True) fs
             exitSuccess
  case opt getPkgClean opts of
     [] -> return ()
     fs -> runIO $ do
             mapM_ (cleanPkg opts) fs
             exitSuccess
  case opt getPkgMkDoc opts of
     [] -> return ()
     fs -> runIO $ do
             mapM_ (documentPkg opts) fs
             exitSuccess
  case opt getPkgTest opts of
     [] -> return ()
     fs -> runIO $ do
             mapM_ (testPkg opts) fs
             exitSuccess
  case opt getPkg opts of
     [] -> return ()
     fs -> runIO $ do
             mapM_ (buildPkg opts (WarnOnly `elem` opts)) fs
             exitSuccess
  case opt getPkgREPL opts of
    []  -> return ()
    [f] -> do replPkg opts f
              runIO exitSuccess
    _   -> ifail "Too many packages"

runIdris :: [Opt] -> Idris ()
runIdris opts = do
  runIO setupBundledCC
  processShowOptions opts
  processClientOptions opts
  processPackageOptions opts
  idrisMain opts

-- Main program reads command line options, parses the main program, and gets
-- on with the REPL.
main :: IO ()
main = do
  opts <- runArgParser
  runMain (runIdris opts)
