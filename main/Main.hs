module Main where

import System.Console.Haskeline
import System.IO
import System.Environment
import System.Exit
import System.FilePath ((</>), addTrailingPathSeparator)

import Data.Maybe
import Data.Version
import Control.Monad.Trans.Error ( ErrorT(..) )
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

main = do opts <- runArgParser
          result <- runErrorT $ execStateT (runIdris opts) idrisInit
          case result of
            Left err -> putStrLn $ "Uncaught error: " ++ show err
            Right _ -> return ()

runIdris :: [Opt] -> Idris ()
runIdris [Client c] = do setVerbose False
                         setQuiet True
                         runIO $ runClient c
runIdris opts = do
       when (ShowIncs `elem` opts) $ runIO showIncs
       when (ShowLibs `elem` opts) $ runIO showLibs
       when (ShowLibdir `elem` opts) $ runIO showLibdir
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
       case opt getPkg opts of
           [] -> case opt getPkgREPL opts of
                      [] -> idrisMain opts
                      [f] -> replPkg f
                      _ -> ifail "Too many packages"
           fs -> runIO $ mapM_ (buildPkg (WarnOnly `elem` opts)) fs

showver = do putStrLn $ "Idris version " ++ ver
             exitWith ExitSuccess

showLibs = do libFlags <- getLibFlags
              putStrLn libFlags
              exitWith ExitSuccess

showLibdir = do dir <- getIdrisLibDir
                putStrLn dir
                exitWith ExitSuccess

showIncs = do incFlags <- getIncFlags
              putStrLn incFlags
              exitWith ExitSuccess
