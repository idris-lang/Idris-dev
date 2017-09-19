#!/usr/bin/env runidris

main : IO () 
main = do
    args <- getArgs
    putStrLn $ "Hello " ++ (show $ drop 1 args) 
