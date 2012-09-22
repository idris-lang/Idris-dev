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

import IRTS.Lang
import IRTS.LParser

import Paths_idris

-- Main program reads command line options, parses the main program, and gets
-- on with the REPL.

main = do xs <- getArgs
          opts <- parseArgs xs
          runInputT defaultSettings $ execStateT (runIdris opts) idrisInit

runIdris :: [Opt] -> Idris ()
runIdris opts = 
    do let inputs = opt getFile opts
       let runrepl = not (NoREPL `elem` opts)
       let output = opt getOutput opts
       let newoutput = opt getNewOutput opts
       let ibcsubdir = opt getIBCSubDir opts
       let importdirs = opt getImportDir opts
       let bcs = opt getBC opts
       let vm = opt getFOVM opts

       when (Ver `elem` opts) $ liftIO showver
       when (Usage `elem` opts) $ liftIO usage
       when (ShowIncs `elem` opts) $ liftIO showIncs
       when (ShowLibs `elem` opts) $ liftIO showLibs
       setREPL runrepl
       setVerbose runrepl
       when (Verbose `elem` opts) $ setVerbose True
       mapM_ makeOption opts
       -- if we have the --fovm flag, drop into the first order VM testing
       case vm of
	    [] -> return ()
	    xs -> liftIO $ mapM_ fovm xs 
       -- if we have the --bytecode flag, drop into the bytecode assembler
       case bcs of
	    [] -> return ()
	    xs -> return () -- liftIO $ mapM_ bcAsm xs 
       case ibcsubdir of
         [] -> setIBCSubDir ""
         (d:_) -> setIBCSubDir d
       setImportDirs importdirs
       elabPrims
       when (not (NoPrelude `elem` opts)) $ do x <- loadModule "prelude"
                                               return ()
       when runrepl $ iputStrLn banner 
       ist <- get
       mods <- mapM loadModule inputs
       ok <- noErrors
       when ok $ case output of
                    [] -> return ()
                    (o:_) -> process "" (Compile ViaC o)  
       when ok $ case newoutput of
                    [] -> return ()
                    (o:_) -> process "" (NewCompile o)  
       when runrepl $ repl ist inputs
       ok <- noErrors
       when (not ok) $ liftIO (exitWith (ExitFailure 1))
  where
    makeOption (OLogging i) = setLogLevel i
    makeOption TypeCase = setTypeCase True
    makeOption TypeInType = setTypeInType True
    makeOption NoCoverage = setCoverage False
    makeOption ErrContext = setErrContext True
    makeOption _ = return ()

getFile :: Opt -> Maybe String
getFile (Filename str) = Just str
getFile _ = Nothing

getBC :: Opt -> Maybe String
getBC (BCAsm str) = Just str
getBC _ = Nothing

getFOVM :: Opt -> Maybe String
getFOVM (FOVM str) = Just str
getFOVM _ = Nothing

getOutput :: Opt -> Maybe String
getOutput (Output str) = Just str
getOutput _ = Nothing

getNewOutput :: Opt -> Maybe String
getNewOutput (NewOutput str) = Just str
getNewOutput _ = Nothing

getIBCSubDir :: Opt -> Maybe String
getIBCSubDir (IBCSubDir str) = Just str
getIBCSubDir _ = Nothing

getImportDir :: Opt -> Maybe String
getImportDir (ImportDir str) = Just str
getImportDir _ = Nothing

opt :: (Opt -> Maybe a) -> [Opt] -> [a]
opt = mapMaybe 

usage = do putStrLn usagemsg
           exitWith ExitSuccess

showver = do putStrLn $ "Idris version " ++ ver
             exitWith ExitSuccess

showLibs = do dir <- getDataDir
              putStrLn $ "-L" ++ dir ++ "/rts -lidris_rts -lgmp -lpthread"
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
parseArgs ("--include":ns)      = liftM (ShowIncs : ) (parseArgs ns)
parseArgs ("--version":ns)      = liftM (Ver : ) (parseArgs ns)
parseArgs ("--verbose":ns)      = liftM (Verbose : ) (parseArgs ns)
parseArgs ("--ibcsubdir":n:ns)  = liftM (IBCSubDir n : ) (parseArgs ns)
parseArgs ("-i":n:ns)           = liftM (ImportDir n : ) (parseArgs ns)
parseArgs ("--bytecode":n:ns)   = liftM (\x -> NoREPL : BCAsm n : x) (parseArgs ns)
parseArgs ("--fovm":n:ns)       = liftM (\x -> NoREPL : FOVM n : x) (parseArgs ns)
parseArgs (n:ns)                = liftM (Filename n : ) (parseArgs ns)

ver = showVersion version

banner = "     ____    __     _                                          \n" ++     
         "    /  _/___/ /____(_)____                                     \n" ++
         "    / // __  / ___/ / ___/     Version " ++ ver ++ "\n" ++
         "  _/ // /_/ / /  / (__  )      http://www.idris-lang.org/      \n" ++
         " /___/\\__,_/_/  /_/____/       Type :? for help                \n" 

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
	   "\t--link            Show library directories and exit (for C linking)\n" ++
	   "\t--include         Show include directories and exit (for C linking)\n"

