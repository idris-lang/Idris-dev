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

data Opt = Filename String
         | Ver
         | Usage
         | NoPrelude
         | NoREPL
         | OLogging Int
         | Output String
         | TypeCase
         | TypeInType
         | NoCoverage 
         | Verbose
    deriving Eq

main = do xs <- getArgs
          opts <- parseArgs xs
          runInputT defaultSettings $ execStateT (runIdris opts) idrisInit

runIdris :: [Opt] -> Idris ()
runIdris opts = 
    do let inputs = opt getFile opts
       let runrepl = not (NoREPL `elem` opts)
       let output = opt getOutput opts
       when (Ver `elem` opts) $ liftIO showver
       when (Usage `elem` opts) $ liftIO usage
       setREPL runrepl
       setVerbose runrepl
       when (Verbose `elem` opts) $ setVerbose True
       mapM_ makeOption opts
       elabPrims
       when (not (NoPrelude `elem` opts)) $ do x <- loadModule "prelude"
                                               return ()
       when runrepl $ iputStrLn banner 
       ist <- get
       mods <- mapM loadModule inputs
       ok <- noErrors
       when ok $ case output of
                    [] -> return ()
                    (o:_) -> process (Compile o)  
       when runrepl $ repl ist inputs
       ok <- noErrors
       when (not ok) $ liftIO (exitWith (ExitFailure 1))
  where
    makeOption (OLogging i) = setLogLevel i
    makeOption TypeCase = setTypeCase True
    makeOption TypeInType = setTypeInType True
    makeOption NoCoverage = setCoverage False
    makeOption _ = return ()

getFile :: Opt -> Maybe String
getFile (Filename str) = Just str
getFile _ = Nothing

getOutput :: Opt -> Maybe String
getOutput (Output str) = Just str
getOutput _ = Nothing

opt :: (Opt -> Maybe a) -> [Opt] -> [a]
opt = mapMaybe 

usage = do putStrLn usagemsg
           exitWith ExitSuccess

showver = do putStrLn $ "Idris version " ++ ver
             exitWith ExitSuccess

parseArgs :: [String] -> IO [Opt]
parseArgs [] = return []
parseArgs ("--log":lvl:ns)   = liftM (OLogging (read lvl) : ) (parseArgs ns)
parseArgs ("--noprelude":ns) = liftM (NoPrelude : ) (parseArgs ns)
parseArgs ("--check":ns)     = liftM (NoREPL : ) (parseArgs ns)
parseArgs ("-o":n:ns)        = liftM (\x -> NoREPL : Output n : x) (parseArgs ns)
parseArgs ("--typecase":ns)  = liftM (TypeCase : ) (parseArgs ns)
parseArgs ("--typeintype":ns) = liftM (TypeInType : ) (parseArgs ns)
parseArgs ("--nocoverage":ns) = liftM (NoCoverage : ) (parseArgs ns)
parseArgs ("--help":ns)      = liftM (Usage : ) (parseArgs ns)
parseArgs ("--version":ns)   = liftM (Ver : ) (parseArgs ns)
parseArgs ("--verbose":ns)   = liftM (Verbose : ) (parseArgs ns)
parseArgs (n:ns)             = liftM (Filename n : ) (parseArgs ns)

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
           "\t--check       Type check only\n" ++
           "\t-o [file]     Generate executable\n" ++
           "\t--noprelude   Don't import the prelude\n" ++
           "\t--typeintype  Disable universe checking\n" ++
           "\t--log [level] Set debugging log level\n"

