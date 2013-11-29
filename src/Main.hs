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

import Util.System ( getLibFlags, getIdrisLibDir, getIncFlags )
import Util.DynamicLinker

import Pkg.Package

import Paths_idris

-- Main program reads command line options, parses the main program, and gets
-- on with the REPL.

main = do xs <- getArgs
          let opts = parseArgs xs
          result <- runErrorT $ execStateT (runIdris opts) idrisInit
          case result of
            Left err -> putStrLn $ "Uncaught error: " ++ show err
            Right _ -> return ()

runIdris :: [Opt] -> Idris ()
runIdris [Client c] = do setVerbose False
                         setQuiet True
                         runIO $ runClient c
runIdris opts = do
       when (Ver `elem` opts) $ runIO showver
       when (Usage `elem` opts) $ runIO usage
       when (ShowIncs `elem` opts) $ runIO showIncs
       when (ShowLibs `elem` opts) $ runIO showLibs
       when (ShowLibdir `elem` opts) $ runIO showLibdir
       case opt getPkgClean opts of
           [] -> return ()
           fs -> do runIO $ mapM_ cleanPkg fs
                    runIO $ exitWith ExitSuccess
       case opt getPkg opts of
           [] -> idrisMain opts -- in Idris.REPL
           fs -> runIO $ mapM_ (buildPkg (WarnOnly `elem` opts)) fs

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
           "\t--quiet           Quiet mode (for editors)\n" ++
           "\t--[no]colour      Control REPL colour highlighting\n" ++
           "\t--check           Type check only\n" ++
           "\t-o [file]         Specify output filename\n" ++
           "\t-i [dir]          Add directory to the list of import paths\n" ++
           "\t--ibcsubdir [dir] Write IBC files into sub directory\n" ++
           "\t--noprelude       Don't import the prelude\n" ++
           "\t--total           Require functions to be total by default\n" ++
           "\t--warnpartial     Warn about undeclared partial functions\n" ++
           "\t--typeintype      Disable universe checking\n" ++
           "\t--log [level]     Type debugging log level\n" ++
           "\t-S                Do no further compilation of code generator output\n" ++
           "\t-c                Compile to object files rather than an executable\n" ++
           "\t--mvn             Create a maven project (for Java codegen)\n" ++
           "\t--exec [expr]     Execute the expression expr in the interpreter,\n" ++
           "\t                  defaulting to Main.main if none provided, and exit.\n" ++
           "\t--ideslave        Ideslave mode (for editors; in/ouput wrapped in \n" ++
           "\t                  s-expressions)\n" ++
           "\t--libdir          Show library install directory and exit\n" ++
           "\t--link            Show C library directories and exit (for C linking)\n" ++
           "\t--include         Show C include directories and exit (for C linking)\n" ++
           "\t--codegen [cg]    Select code generator: C, Java, bytecode, javascript,\n" ++
           "\t                  node or llvm\n" ++
           "\t--target [triple] Select target triple (for LLVM codegen)\n" ++
           "\t--cpu [cpu]       Select target CPU (e.g. corei7 or cortex-m3) (for LLVM codegen)\n"


