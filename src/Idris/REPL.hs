{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances, DeriveFunctor #-}

module Idris.REPL where

import Idris.AbsSyntax
import Idris.REPLParser
import Idris.ElabDecls
import Idris.Error
import Idris.Delaborate
import Idris.Compiler
import Idris.Prover

import Core.Evaluate
import Core.ProofShell
import Core.TT

import System.Console.Readline
import Control.Monad
import Control.Monad.State
import Data.List

repl :: String -> Idris ()
repl prompt
     = do x <- lift $ readline (prompt ++ "> ")
          case x of
              Nothing -> repl prompt
              Just input -> do lift $ addHistory input
                               continue <- processInput input
                               when continue (repl prompt)

processInput :: String -> Idris Bool
processInput cmd
    = do i <- get
         case parseCmd i cmd of
                Left err ->   do lift $ print err
                                 return True
                Right Quit -> do iputStrLn "Bye bye"
                                 return False
                Right cmd  -> do idrisCatch (process cmd)
                                            (\e -> iputStrLn (report e))
                                 return True

process :: Command -> Idris ()
process Help 
    = iputStrLn "At some point I'll write some help text. Thanks for asking though."
process (Eval t) = do (tm, ty) <- elabVal toplevel t
                      ctxt <- getContext
                      ist <- get 
                      let tm' = normalise ctxt [] tm
                      let ty' = normalise ctxt [] ty
                      logLvl 3 $ "Raw: " ++ show tm'
                      iputStrLn (show (delab ist tm') ++ " : " ++ 
                                 show (delab ist ty'))
process (Spec t) = do (tm, ty) <- elabVal toplevel t
                      ctxt <- getContext
                      ist <- get
                      let tm' = specialise ctxt (idris_statics ist) tm
                      iputStrLn (show (delab ist tm'))
process (Prove n) = prover n
process (HNF t)  = do (tm, ty) <- elabVal toplevel t
                      ctxt <- getContext
                      ist <- get
                      let tm' = hnf ctxt [] tm
                      iputStrLn (show (delab ist tm'))
process TTShell  = do ist <- get
                      let shst = initState (tt_ctxt ist)
                      shst' <- lift $ runShell shst
                      return ()
process (Compile f) = do compile f 
process (LogLvl i) = setLogLevel i 
process Metavars = do ist <- get
                      let mvs = idris_metavars ist \\ primDefs
                      case mvs of
                        [] -> iputStrLn "No global metavariables to solve"
                        _ -> iputStrLn $ "Global metavariables:\n\t" ++ show mvs
process NOP      = return ()

