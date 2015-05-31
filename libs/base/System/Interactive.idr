||| Various helper functions for creating simple interactive systems.
||| 
||| These are mostly intended for helping with teaching, in that they will allow
||| the easy creation of interactive programs without needing to teach IO
||| or Effects first, but they also capture some common patterns of interactive
||| programming.
module System.Interactive

{-
When the interfaces and names are stable, these are intended for the Prelude.
-}

import System

||| Process input from an open file handle, while maintaining a state.
||| @ state the input state
||| @ onRead the function to run on reading a line, returning a String to
||| output and a new state
||| @ onEOF the function to run on reaching end of file, returning a String
||| to output
public partial
processHandle : File -> 
                (state : a) ->
                (onRead : a -> String -> (String, a)) -> 
                (onEOF : a -> String) -> 
                IO ()
processHandle h acc onRead onEOF 
   = if !(feof h)
        then putStr (onEOF acc)
        else do x <- fread h
                let (out, acc') = onRead acc x
                putStr out
                processHandle h acc' onRead onEOF    

||| Process input from the standard input stream, while maintaining a state.
||| @ state the input state
||| @ onRead the function to run on reading a line, returning a String to
||| output and a new state
||| @ onEOI the function to run on reaching end of input, returning a String
||| to output
public partial
processStdin : (state : a) -> 
               (onRead : a -> String -> (String, a)) -> 
               (onEOI : a -> String) -> IO ()
processStdin = processHandle stdin

||| A basic read-eval-print loop, maintaining a state
||| @ state the input state
||| @ prompt the prompt to show 
||| @ onInput the function to run on reading input, returning a String to
||| output and a new state. Returns Nothing if the repl should exit
public partial
replWith : (state : a) -> (prompt : String) -> 
           (onInput : a -> String -> Maybe (String, a)) -> IO a
replWith acc prompt fn 
   = do putStr prompt
        x <- getLine
        case fn acc x of
             Just (out, acc') => do putStr out 
                                    replWith acc' prompt fn
             Nothing => return acc

||| A basic read-eval-print loop
||| @ prompt the prompt to show 
||| @ onInput the function to run on reading input, returning a String to
||| output 
public partial
repl : (prompt : String) -> 
       (onInput : String -> String) -> IO ()
repl prompt fn 
   = do replWith () prompt (\x, s => Just (fn s, ()))
        return ()

