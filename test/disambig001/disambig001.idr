module Main

import Prelude.Monad

import System
import Effect.System

main : IO ()
main = do 
    args <- System.getArgs
    putStrLn (concat (drop 1 args))

