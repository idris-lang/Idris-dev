module Main where

import System.Console.Readline
import System.IO
import System.Environment
import System.Exit

import Data.Maybe
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


-- Main program reads command line options, parses the main program, and gets
-- on with the REPL.

data Opt = Filename String
         | Version
         | OLogging
    deriving Eq

main = do xs <- getArgs
          opts <- parseArgs xs
          execStateT (runIdris opts) idrisInit

runIdris :: [Opt] -> Idris ()
runIdris opts = 
    do let inputs = opt getFile opts
       when (OLogging `elem` opts) (setOpt Logging True)
       mapM_ loadModule inputs       
       repl

loadModule :: FilePath -> Idris ()
loadModule f = do iLOG ("Reading " ++ show f)
                  return ()

getFile :: Opt -> Maybe String
getFile (Filename str) = Just str
getFile _ = Nothing

opt :: (Opt -> Maybe a) -> [Opt] -> [a]
opt = mapMaybe 

usage = do putStrLn "You're doing it wrong"
           exitWith (ExitFailure 1)

parseArgs :: [String] -> IO [Opt]
parseArgs [] = return []
parseArgs ("--log":ns) = liftM (OLogging : ) (parseArgs ns)
parseArgs (n:ns)       = liftM (Filename n : ) (parseArgs ns)

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

