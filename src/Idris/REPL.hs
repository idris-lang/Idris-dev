{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances, DeriveFunctor #-}

module Idris.REPL where

import Idris.AbsSyntax
import Idris.REPLParser
import Idris.ElabDecls

import Core.Evaluate
import Core.ProofShell
import Core.TT

import System.Console.Readline
import Control.Monad
import Control.Monad.State


repl :: Idris ()
repl = do x <- lift $ readline "Idris> "
          case x of
              Nothing -> repl
              Just input -> do lift $ addHistory input
                               continue <- processInput input
                               when continue repl

processInput :: String -> Idris Bool
processInput cmd
    = do i <- get
         case parseCmd i cmd of
                Left err ->   do lift $ print err
                                 return True
                Right Quit -> do iputStrLn "Bye bye"
                                 return False
                Right cmd  -> do process cmd
                                 return True

process :: Command -> Idris ()
process Help 
    = iputStrLn "At some point I'll write some help text. Thanks for asking though."
process (Eval t) = do (tm, ty) <- elabVal t
                      ctxt <- getContext
                      let tm' = normalise ctxt [] tm
                      iputStrLn (show tm' ++ " : " ++ show ty)
process TTShell  = do ist <- get
                      let shst = initState (tt_ctxt ist)
                      shst' <- lift $ runShell shst
                      return ()
process NOP      = return ()

