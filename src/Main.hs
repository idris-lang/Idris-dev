module Main where

import System.Console.Haskeline
import System.IO
import System.Environment
import System.Exit

import Data.Maybe
import Data.Version
import Control.Monad.State

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

import Paths_idris

-- Main program reads command line options, parses the main program, and gets
-- on with the REPL.

main = do xs <- getArgs
          opts <- parseArgs xs
          runInputT defaultSettings $ execStateT (runIdris opts) idrisInit

runIdris :: [Opt] -> Idris ()
runIdris opts = do
       when (Ver `elem` opts) $ liftIO showver
       when (Usage `elem` opts) $ liftIO usage
       when (ShowIncs `elem` opts) $ liftIO showIncs
       when (ShowLibs `elem` opts) $ liftIO showLibs
       when (ShowLibdir `elem` opts) $ liftIO showLibdir
       idrisMain opts -- in Idris.REPL

usage = do putStrLn usagemsg
           exitWith ExitSuccess

showver = do putStrLn $ "Idris version " ++ ver
             exitWith ExitSuccess

showLibs = do dir <- getDataDir
              putStrLn $ "-L" ++ dir ++ "/rts -lidris_rts -lgmp -lpthread"
              exitWith ExitSuccess

showLibdir = do dir <- getDataDir
                putStrLn $ dir ++ "/"
                exitWith ExitSuccess

showIncs = do dir <- getDataDir
              putStrLn $ "-I" ++ dir ++ "/rts"
              exitWith ExitSuccess

parseArgs :: [String] -> IO [Opt]
parseArgs [] = return []
parseArgs ("--log":lvl:ns)      = liftM (OLogging (read lvl) : ) (parseArgs ns)
parseArgs ("--noprelude":ns)    = liftM (NoPrelude : ) (parseArgs ns)
parseArgs ("--check":ns)        = liftM (NoREPL : ) (parseArgs ns)
parseArgs ("-o":n:ns)           = liftM (\x -> NoREPL : Output n : x) (parseArgs ns)
parseArgs ("-no":n:ns)          = liftM (\x -> NoREPL : NewOutput n : x) (parseArgs ns)
parseArgs ("--typecase":ns)     = liftM (TypeCase : ) (parseArgs ns)
parseArgs ("--typeintype":ns)   = liftM (TypeInType : ) (parseArgs ns)
parseArgs ("--nocoverage":ns)   = liftM (NoCoverage : ) (parseArgs ns)
parseArgs ("--errorcontext":ns) = liftM (ErrContext : ) (parseArgs ns)
parseArgs ("--help":ns)         = liftM (Usage : ) (parseArgs ns)
parseArgs ("--link":ns)         = liftM (ShowLibs : ) (parseArgs ns)
parseArgs ("--libdir":ns)       = liftM (ShowLibdir : ) (parseArgs ns)
parseArgs ("--include":ns)      = liftM (ShowIncs : ) (parseArgs ns)
parseArgs ("--version":ns)      = liftM (Ver : ) (parseArgs ns)
parseArgs ("--verbose":ns)      = liftM (Verbose : ) (parseArgs ns)
parseArgs ("--ibcsubdir":n:ns)  = liftM (IBCSubDir n : ) (parseArgs ns)
parseArgs ("-i":n:ns)           = liftM (ImportDir n : ) (parseArgs ns)
parseArgs ("--bytecode":n:ns)   = liftM (\x -> NoREPL : BCAsm n : x) (parseArgs ns)
parseArgs ("--fovm":n:ns)       = liftM (\x -> NoREPL : FOVM n : x) (parseArgs ns)
parseArgs (n:ns)                = liftM (Filename n : ) (parseArgs ns)

usagemsg = "Idris version " ++ ver ++ "\n" ++
           "--------------" ++ map (\x -> '-') ver ++ "\n" ++
           "Usage: idris [input file] [options]\n" ++
           "Options:\n" ++
           "\t--check           Type check only\n" ++
           "\t-o [file]         Generate executable\n" ++
           "\t-i [dir]          Add directory to the list of import paths\n" ++
           "\t--ibcsubdir [dir] Write IBC files into sub directory\n" ++
           "\t--noprelude       Don't import the prelude\n" ++
           "\t--typeintype      Disable universe checking\n" ++
           "\t--log [level]     Set debugging log level\n" ++
	   "\t--libdir          Show library install directory and exit\n" ++
	   "\t--link            Show C library directories and exit (for C linking)\n" ++
	   "\t--include         Show C include directories and exit (for C linking)\n"

