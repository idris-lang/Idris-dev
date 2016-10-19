||| Various helper functions for creating simple interactive systems.
|||
||| These are mostly intended for helping with teaching, in that they will allow
||| the easy creation of interactive programs without needing to teach IO
||| or Effects first, but they also capture some common patterns of interactive
||| programming.
module Prelude.Interactive

import Builtins
import Prelude.List
import Prelude.File
import Prelude.Bool
import Prelude.Interfaces
import Prelude.Strings
import Prelude.Chars
import Prelude.Show
import Prelude.Cast
import Prelude.Maybe
import Prelude.Functor
import Prelude.Either
import Prelude.Monad
import IO

%access public export

---- some basic io

||| Output a string to stdout without a trailing newline, for any FFI
||| descriptor
putStr' : String -> IO' ffi ()
putStr' x = do prim_write x
               pure ()

||| Output a string to stdout without a trailing newline
putStr : String -> IO ()
putStr = putStr'

||| Output a string to stdout with a trailing newline, for any FFI
||| descriptor
putStrLn' : String -> IO' ffi ()
putStrLn' x = putStr' (x ++ "\n")

||| Output a string to stdout with a trailing newline
putStrLn : String -> IO ()
putStrLn = putStrLn'

||| Output something showable to stdout, without a trailing newline, for any FFI
||| descriptor
print' : Show ty => ty -> IO' ffi ()
print' x = putStr' (show x)

||| Output something showable to stdout, without a trailing newline
print : Show ty => ty -> IO ()
print = print'

||| Output something showable to stdout, with a trailing newline, for any FFI
||| descriptor
printLn' : Show ty => ty -> IO' ffi ()
printLn' x = putStrLn' (show x)

||| Output something showable to stdout, with a trailing newline
printLn : Show ty => ty -> IO ()
printLn = printLn'

||| Read one line of input from stdin, without the trailing newline, for any FFI
||| descriptor
getLine' : IO' ffi String
getLine' = do x <- prim_read
              pure (reverse (trimNL (reverse x)))
  where trimNL : String -> String
        trimNL str with (strM str)
          trimNL "" | StrNil = ""
          trimNL (strCons '\n' xs) | StrCons _ _ = xs
          trimNL (strCons x xs)    | StrCons _ _ = strCons x xs

||| Read one line of input from stdin, without the trailing newline
getLine : IO String
getLine = getLine'

||| Write a single character to stdout
putChar : Char -> IO ()
putChar c = foreign FFI_C "putchar" (Int -> IO ()) (cast c)

||| Write a singel character to stdout, with a trailing newline
putCharLn : Char -> IO ()
putCharLn c = putStrLn (singleton c)

||| Read a single character from stdin
getChar : IO Char
getChar = map cast $ foreign FFI_C "getchar" (IO Int)

||| Disables buffering in both stdin and stdout:
||| so that output is written immediately (never stored in the buffer)
||| and the next input item is read and returned
|||
||| this is useful to circumvent problems with IO on some Windows systems
||| where stdout output right before a prompt is only shown after
||| the input-line from stdin is produced
disableBuffering : IO ()
disableBuffering = foreign FFI_C "idris_disableBuffering" (IO ())

||| Get the command-line arguments that the program was called with.
partial
getArgs : IO (List String)
getArgs = do n <- numArgs
             ga' [] 0 n
  where
    numArgs : IO Int
    numArgs = foreign FFI_C "idris_numArgs" (IO Int)

    getArg : Int -> IO String
    getArg x = foreign FFI_C "idris_getArg" (Int -> IO String) x

    partial
    ga' : List String -> Int -> Int -> IO (List String)
    ga' acc i n = if (i == n) then (pure $ reverse acc) else
                    do arg <- getArg i
                       ga' (arg :: acc) (i+1) n


||| Process input from an open file handle, while maintaining a state.
||| @ state the input state
||| @ onRead the function to run on reading a line, returning a String to
||| output and a new state
||| @ onEOF the function to run on reaching end of file, returning a String
||| to output
partial
processHandle : File ->
                (state : a) ->
                (onRead : a -> String -> (String, a)) ->
                (onEOF : a -> String) ->
                IO ()
processHandle h acc onRead onEOF
   = if !(fEOF h)
        then putStr (onEOF acc)
        else do Right x <- fGetLine h
                    | Left err => putStr (onEOF acc)
                let (out, acc') = onRead acc x
                putStr out
                processHandle h acc' onRead onEOF

||| Process input from the standard input stream, while maintaining a state.
||| @ state the input state
||| @ onRead the function to run on reading a line, returning a String to
||| output and a new state
||| @ onEOI the function to run on reaching end of input, returning a String
||| to output
partial
processStdin : (state : a) ->
               (onRead : a -> String -> (String, a)) ->
               (onEOI : a -> String) -> IO ()
processStdin = processHandle stdin

||| A basic read-eval-print loop, maintaining a state
||| @ state the input state
||| @ prompt the prompt to show
||| @ onInput the function to run on reading input, returning a String to
||| output and a new state. Returns Nothing if the repl should exit
partial
replWith : (state : a) -> (prompt : String) ->
           (onInput : a -> String -> Maybe (String, a)) -> IO ()
replWith acc prompt fn
   = do putStr prompt
        x <- getLine
        case fn acc x of
             Just (out, acc') => do putStr out
                                    replWith acc' prompt fn
             Nothing => pure ()

||| A basic read-eval-print loop
||| @ prompt the prompt to show
||| @ onInput the function to run on reading input, returning a String to
||| output
partial
repl : (prompt : String) ->
       (onInput : String -> String) -> IO ()
repl prompt fn
   = replWith () prompt (\x, s => Just (fn s, ()))
