module Main where

import System.Console.Readline
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

import Idris.AbsSyntax
import Idris.Parser
import Idris.REPL
import Idris.ElabDecls
import Idris.Primitives
import Idris.Imports
import Paths_miniidris

-- Main program reads command line options, parses the main program, and gets
-- on with the REPL.

data Opt = Filename String
         | Version
         | NoPrelude
         | NoREPL
         | OLogging Int
    deriving Eq

main = do xs <- getArgs
          opts <- parseArgs xs
          execStateT (runIdris opts) idrisInit

runIdris :: [Opt] -> Idris ()
runIdris opts = 
    do let inputs = opt getFile opts
       let runrepl = not (NoREPL `elem` opts)
       mapM_ makeOption opts
       elabPrims
       when (not (NoPrelude `elem` opts)) $ do x <- loadModule "prelude"
                                               return ()
       when runrepl $ iputStrLn banner 
       mods <- mapM loadModule inputs       
       when runrepl $ repl (mkPrompt mods)
  where
    makeOption (OLogging i) = setLogLevel i
    makeOption _ = return ()

mkPrompt [] = "Idris"
mkPrompt [x] = "*" ++ x
mkPrompt (x:xs) = "*" ++ x ++ " " ++ mkPrompt xs

getFile :: Opt -> Maybe String
getFile (Filename str) = Just str
getFile _ = Nothing

opt :: (Opt -> Maybe a) -> [Opt] -> [a]
opt = mapMaybe 

usage = do putStrLn "You're doing it wrong"
           exitWith (ExitFailure 1)

parseArgs :: [String] -> IO [Opt]
parseArgs [] = return []
parseArgs ("--log":lvl:ns)   = liftM (OLogging (read lvl) : ) (parseArgs ns)
parseArgs ("--noprelude":ns) = liftM (NoPrelude : ) (parseArgs ns)
parseArgs ("--check":ns)     = liftM (NoREPL : ) (parseArgs ns)
parseArgs (n:ns)             = liftM (Filename n : ) (parseArgs ns)

{-
main'
     = do f <- readFile "test.mi"
          case parseFile f of
              Left err -> print err
              Right defs -> do
                print defs
                case checkProgram emptyContext defs of
                    OK ctxt -> do print (toAlist ctxt) 
                                  runShell (initState ctxt)
                                  return ()
                    err -> print err
                    -}

ver = showVersion version

banner = "     ____    __     _                                          \n" ++     
         "    /  _/___/ /____(_)____                                     \n" ++
         "    / // __  / ___/ / ___/     Version " ++ ver ++ "\n" ++
         "  _/ // /_/ / /  / (__  )      http://www.idris-lang.org/      \n" ++
         " /___/\\__,_/_/  /_/____/       Type :? for help                \n" 

