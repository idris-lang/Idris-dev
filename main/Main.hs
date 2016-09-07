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

check :: [Opt] -> (Opt -> Maybe a) -> ([a] -> Idris ()) -> Idris ()
check opts extractOpts action = do
  case opt extractOpts opts of
    [] -> return ()
    fs -> do action fs
             runIO exitSuccess

processClientOptions :: [Opt] -> Idris ()
processClientOptions opts = check opts getClient $ \fs -> case fs of
  (c : _) -> do
    setVerbose False
    setQuiet True
    runIO $ runClient (getPort opts) c

processPackageOptions :: [Opt] -> Idris ()
processPackageOptions opts = do
  check opts getPkgCheck $ \fs -> runIO $ do
    mapM_ (checkPkg opts (WarnOnly `elem` opts) True) fs
  check opts getPkgClean $ \fs -> runIO $ do
    mapM_ (cleanPkg opts) fs
  check opts getPkgMkDoc $ \fs -> runIO $ do
    mapM_ (documentPkg opts) fs
  check opts getPkgTest $ \fs -> runIO $ do
    mapM_ (testPkg opts) fs
  check opts getPkg $ \fs -> runIO $ do
    mapM_ (buildPkg opts (WarnOnly `elem` opts)) fs
  check opts getPkgREPL $ \fs -> case fs of
    [f] -> replPkg opts f
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
