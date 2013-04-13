module Main

import System
import Parser
import Solver

main : IO ()
main = do
  f <- readFile "/dev/stdin"
  case parse f of
    Left err => putStrLn err
    Right (_ ** (board ** legal)) => do
      putStrLn "Got board:"
      print board
      putStrLn "Solving..."
      case fillBoard board legal of
        Nothing => putStrLn "No solution found"
        Just (solved ** _) => do
          putStrLn "Solution found:"
          print solved
