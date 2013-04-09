module Main

import Parser
import System

main : IO ()
main = do
  args <- getArgs
  case args of
    [_, path] => do
      putStrLn ("Reading " ++ path)
      f <- readFile path
      case parse f of
        Left err => putStrLn err
        Right (size ** (board ** _)) => putStrLn ("Got board:\n" ++ show board)
    _ => putStrLn "Expected path"
