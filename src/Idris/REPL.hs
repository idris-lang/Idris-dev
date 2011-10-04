{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances, DeriveFunctor #-}

module Idris.REPL where

import Idris.AbsSyntax
import Idris.REPLParser

import System.Console.Readline
import Control.Monad
import Control.Monad.State


repl :: Idris ()
repl = do x <- lift $ readline "Idris> "
          case x of
              Nothing -> repl
              Just input -> do continue <- processInput input
                               when continue repl

processInput :: String -> Idris Bool
processInput cmd
    = case parseCmd cmd of
                Left err ->   do lift $ print err
                                 return True
                Right Quit -> do iputStrLn "Bye bye"
                                 return False
                Right cmd  -> do process cmd
                                 return True

process :: Command -> Idris ()
process Help = iputStrLn "At some point I'll write some help text. Thanks for asking though."

