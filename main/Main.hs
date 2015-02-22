module Main where

import System.Console.Haskeline
import System.IO
import System.Environment
import System.Info
import System.Exit
import System.FilePath ((</>), addTrailingPathSeparator)
import System.Directory

import Data.Maybe
import Data.Version
import Control.Monad.Trans.State.Strict ( execStateT, get, put )
import Control.Monad ( when )

import Idris.Core.TT
import Idris.Core.Typecheck
import Idris.Core.Evaluate
import Idris.Core.Constraints

import Idris.AbsSyntax
import Idris.Parser
import Idris.REPL
import Idris.ElabDecls
import Idris.Primitives
import Idris.Imports
import Idris.Error
import Idris.CmdOptions

import IRTS.System ( getLibFlags, getIdrisLibDir, getIncFlags )

import Util.DynamicLinker

import Pkg.Package

import Paths_idris

-- Main program reads command line options, parses the main program, and gets
-- on with the REPL.

main :: IO ()
main = do
          when (os == "mingw32") $  do hSetEncoding stdout utf8
          opts <- runArgParser
          runMain (runIdris opts)

runIdris :: [Opt] -> Idris ()
runIdris opts = do
       when (ShowIncs `elem` opts) $ runIO showIncs
       when (ShowLibs `elem` opts) $ runIO showLibs
       when (ShowLibdir `elem` opts) $ runIO showLibdir
       when (ShowPkgs `elem` opts) $ runIO showPkgs
       case opt getClient opts of
           []    -> return ()
           (c:_) -> do setVerbose False
                       setQuiet True
                       runIO $ runClient (getPort opts) c
                       runIO $ exitWith ExitSuccess
       case opt getPkgCheck opts of
           [] -> return ()
           fs -> do runIO $ mapM_ (checkPkg (WarnOnly `elem` opts) True) fs
                    runIO $ exitWith ExitSuccess
       case opt getPkgClean opts of
           [] -> return ()
           fs -> do runIO $ mapM_ cleanPkg fs
                    runIO $ exitWith ExitSuccess
       case opt getPkgMkDoc opts of                -- IdrisDoc
           [] -> return ()
           fs -> do runIO $ mapM_ documentPkg fs
                    runIO $ exitWith ExitSuccess
       case opt getPkgTest opts of
           [] -> return ()
           fs -> do runIO $ mapM_ testPkg fs
                    runIO $ exitWith ExitSuccess
       case opt getPkg opts of
           [] -> case opt getPkgREPL opts of
                      [] -> idrisMain opts
                      [f] -> replPkg f
                      _ -> ifail "Too many packages"
           fs -> runIO $ mapM_ (buildPkg (WarnOnly `elem` opts)) fs

showver :: IO b
showver = do putStrLn $ "Idris version " ++ ver
             exitWith ExitSuccess

showLibs :: IO b
showLibs = do libFlags <- getLibFlags
              putStrLn $ unwords libFlags
              exitWith ExitSuccess

showLibdir :: IO b
showLibdir = do dir <- getIdrisLibDir
                putStrLn dir
                exitWith ExitSuccess

showIncs :: IO b
showIncs = do incFlags <- getIncFlags
              putStrLn $ unwords incFlags
              exitWith ExitSuccess

-- | List idris packages installed
showPkgs :: IO b
showPkgs = do mapM putStrLn =<< installedPackages
              exitWith ExitSuccess
