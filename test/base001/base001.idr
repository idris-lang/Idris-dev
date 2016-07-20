module Main

import System

main : IO ()
main = do 
  ec <- system "exit 1"
  printLn ec
  printLn $ ec == 1
