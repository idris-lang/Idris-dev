module Main

import Effects
import Effect.StdIO
import Effect.State

hello : { [STATE Int, STDIO] } Eff ()
hello = do putStr "Name? "
           putStrLn ("Hello " ++ trim !getStr ++ "!")
           update (+1)
           putStrLn ("I've said hello to: " ++ show !get ++ " people")
           hello

main : IO ()
main = run hello
