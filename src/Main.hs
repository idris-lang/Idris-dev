module Main where

import System.Exit ( ExitCode(..), exitWith, exitSuccess )

import Control.Monad ( unless, when, (>=>) )
import Data.Maybe    ( fromMaybe )
import Data.Foldable ( foldrM )

import Idris.AbsSyntax
import Idris.CmdOptions
import Idris.Error
import Idris.Info.Show
import Idris.Main
import Idris.Package

import System.Exit ( ExitCode(..), exitWith)

#ifdef FREESTANDING
import Data.List (intercalate)
import System.Directory (doesDirectoryExist)
import System.Environment (getEnv, getExecutablePath, setEnv)
import System.FilePath (dropFileName, isAbsolute, searchPathSeparator)
import Tools_idris
#endif

setupBundledCC :: IO()
#ifdef FREESTANDING
setupBundledCC = when hasBundledToolchain
                    $ do
                        exePath <- getExecutablePath
                        path <- getEnv "PATH"
                        tcDir <- return getToolchainDir
                        absolute <- return $ isAbsolute tcDir
                        target <- return $
                                    if absolute
                                       then tcDir
                                       else dropFileName exePath ++ tcDir
                        present <- doesDirectoryExist target
                        when present $ do
                          newPath <- return $ intercalate [searchPathSeparator] [target, path]
                          setEnv "PATH" newPath
#else
setupBundledCC = return ()
#endif

processShowOptions :: [Opt] -> Idris ()
processShowOptions opts = runIO $ do
  when (ShowAll `elem` opts)          $ showExitIdrisInfo
  when (ShowLoggingCats `elem` opts)  $ showExitIdrisLoggingCategories
  when (ShowIncs `elem` opts)         $ showExitIdrisFlagsInc
  when (ShowLibs `elem` opts)         $ showExitIdrisFlagsLibs
  when (ShowLibDir `elem` opts)       $ showExitIdrisLibDir
  when (ShowDocDir `elem` opts)       $ showExitIdrisDocDir
  when (ShowPkgs `elem` opts)         $ showExitIdrisInstalledPackages

check :: [Opt] -> (Opt -> Maybe a) -> ([a] -> Idris ()) -> Idris ()
check opts extractOpts action = do
  case opt extractOpts opts of
    [] -> return ()
    fs -> do action fs
             runIO exitSuccess

processClientOptions :: [Opt] -> Idris ()
processClientOptions opts = check opts getClient $ \fs -> case fs of
  []      -> ifail "No --client argument. This indicates a bug. Please report."
  (c : _) -> do
    setVerbose False
    setQuiet True
    case getPort opts of
      Just  DontListen       -> ifail "\"--client\" and \"--port none\" are incompatible"
      Just (ListenPort port) -> runIO $ runClient (Just port) c
      Nothing                -> runIO $ runClient Nothing c

processPackageOptions :: [Opt] -> Idris ()
processPackageOptions opts = do
  check opts getPkgCheck $ \fs -> runIO $ do
    mapM_ (checkPkg opts (WarnOnly `elem` opts) True) fs
  check opts getPkgClean $ \fs -> runIO $ do
    mapM_ (cleanPkg opts) fs
  check opts getPkgMkDoc $ \fs -> runIO $ do
    mapM_ (documentPkg opts) fs
  check opts getPkgTest $ \fs -> runIO $ do

    codes <- mapM (testPkg opts) fs
    -- check if any of the tests exited with an exit code other
    -- than zero; if they did, exit with exit code 1
    unless (null $ filter (/= ExitSuccess) codes) $
       exitWith (ExitFailure 1)

  check opts getPkg $ \fs -> runIO $ do
    mapM_ (buildPkg opts (WarnOnly `elem` opts)) fs
  check opts getPkgREPL $ \fs -> case fs of
    [f] -> replPkg opts f
    _   -> ifail "Too many packages"

-- | The main function for the Idris executable.
runIdris :: [Opt] -> Idris ()
runIdris opts = do
  runIO setupBundledCC
  processShowOptions opts    -- Show information then quit.
  processClientOptions opts  -- Be a client to a REPL server.
  processPackageOptions opts -- Work with Idris packages.
  idrisMain opts             -- Launch REPL or compile mode.

-- Main program reads command line options, parses the main program, and gets
-- on with the REPL.
main :: IO ()
main = do
  opts <- runArgParser
  runMain (runIdris opts)
