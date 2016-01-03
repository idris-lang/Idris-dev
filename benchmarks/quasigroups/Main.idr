module Main

import System
import Parser
import Solver

main : IO ()
main = do
  args <- getArgs
  case args of
    [_, path] => do
      f <- readFile path
      case f of
        Left _err => putStrLn $ "Error reading file: " ++ path
        Right f' =>
          case parse f' of
            Left err => putStrLn err
            Right (_ ** (board ** legal)) => do
              putStrLn "Got board:"
              printLn board
              putStrLn "Solving..."
              case fillBoard board legal of
                Nothing => putStrLn "No solution found"
                Just (solved ** _) => do
                  putStrLn "Solution found:"
                  printLn solved
    [self] => putStrLn ("Usage: " ++ self ++ " <board file>")
