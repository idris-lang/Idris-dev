module Main where

import System.Console.Haskeline
import System.IO
import System.Environment
import System.Exit
import System.FilePath ((</>), addTrailingPathSeparator)

import Data.Maybe
import Data.Version
import Control.Monad.Trans.State.Strict ( execStateT, get, put )
import Control.Monad.Trans ( liftIO )
import Control.Monad ( when )

import Core.CoreParser
import Core.ShellParser
import Core.TT
import Core.Typecheck
import Core.ProofShell
import Core.Evaluate
import Core.Constraints

import Idris.AbsSyntax
import Idris.Parser
import Idris.REPL
import Idris.ElabDecls
import Idris.Primitives
import Idris.Imports
import Idris.Error

import Util.System ( getLibFlags, getIdrisLibDir, getIncFlags )

import Pkg.Package

import Paths_idris

-- Main program reads command line options, parses the main program, and gets
-- on with the REPL.

main = do xs <- getArgs
          let opts = parseArgs xs
          runInputT defaultSettings $ execStateT (runIdris opts) idrisInit

runIdris :: [Opt] -> Idris ()
runIdris opts = do
       when (Ver `elem` opts) $ liftIO showver
       when (Usage `elem` opts) $ liftIO usage
       when (ShowIncs `elem` opts) $ liftIO showIncs
       when (ShowLibs `elem` opts) $ liftIO showLibs
       when (ShowLibdir `elem` opts) $ liftIO showLibdir
       case opt getPkgClean opts of
           [] -> return ()
           fs -> do liftIO $ mapM_ cleanPkg fs
                    liftIO $ exitWith ExitSuccess
       case opt getPkg opts of
           [] -> idrisMain opts -- in Idris.REPL
           fs -> liftIO $ mapM_ (buildPkg (WarnOnly `elem` opts)) fs

usage = do putStrLn usagemsg
           exitWith ExitSuccess

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

usagemsg = "Idris version " ++ ver ++ "\n" ++
           "--------------" ++ map (\x -> '-') ver ++ "\n" ++
           "Usage: idris [input file] [options]\n" ++
           "Options:\n" ++
           "\t--check           Type check only\n" ++
           "\t-o [file]         Specify output filename\n" ++
           "\t-i [dir]          Add directory to the list of import paths\n" ++
           "\t--ibcsubdir [dir] Write IBC files into sub directory\n" ++
           "\t--noprelude       Don't import the prelude\n" ++
           "\t--total           Require functions to be total by default\n" ++
           "\t--warnpartial     Warn about undeclared partial functions\n" ++
           "\t--typeintype      Disable universe checking\n" ++
           "\t--log [level]     Set debugging log level\n" ++
           "\t-S                Do no further compilation of code generator output\n" ++
           "\t-c                Compile to object files rather than an executable\n" ++
           "\t--libdir          Show library install directory and exit\n" ++
           "\t--link            Show C library directories and exit (for C linking)\n" ++
           "\t--include         Show C include directories and exit (for C linking)\n"
