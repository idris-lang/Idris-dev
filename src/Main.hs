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
import Idris.ElabDecls
import Idris.Primitives

-- Main program reads command line options, parses the main program, and gets
-- on with the REPL.

data Opt = Filename String
         | Version
         | OLogging Int
    deriving Eq

main = do xs <- getArgs
          opts <- parseArgs xs
          execStateT (runIdris opts) idrisInit

runIdris :: [Opt] -> Idris ()
runIdris opts = 
    do let inputs = opt getFile opts
       mapM_ makeOption opts
       elabPrims
       mapM_ loadModule inputs       
       repl
  where
    makeOption (OLogging i) = setLogLevel i
    makeOption _ = return ()

loadModule :: FilePath -> Idris ()
loadModule f = do iLOG ("Reading " ++ show f)
                  ds <- parseProg defaultSyntax f
                  iLOG (dumpDecls ds)
                  i <- get
                  iLOG (show (idris_infixes i))
                  -- Now add all the declarations to the context
                  mapM_ elabDecl ds
                  return ()

dumpDecls :: [PDecl] -> String
dumpDecls [] = ""
dumpDecls (d:ds) = dumpDecl d ++ "\n" ++ dumpDecls ds

dumpDecl (PFix f ops) = show f ++ " " ++ showSep ", " ops 
dumpDecl (PTy n t) = "tydecl " ++ show n ++ " : " ++ showImp True t
dumpDecl (PClauses n cs) = "pat\t" ++ showSep "\n\t" (map (showCImp True) cs)
dumpDecl (PData d) = showDImp True d

getFile :: Opt -> Maybe String
getFile (Filename str) = Just str
getFile _ = Nothing

opt :: (Opt -> Maybe a) -> [Opt] -> [a]
opt = mapMaybe 

usage = do putStrLn "You're doing it wrong"
           exitWith (ExitFailure 1)

parseArgs :: [String] -> IO [Opt]
parseArgs [] = return []
parseArgs ("--log":lvl:ns) = liftM (OLogging (read lvl) : ) (parseArgs ns)
parseArgs (n:ns)           = liftM (Filename n : ) (parseArgs ns)

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

