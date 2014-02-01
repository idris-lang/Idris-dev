module Effect.StdIO

import Effects
import Control.IOExcept

data StdIO : Effect where
     PutStr : String -> { () } StdIO () 
     GetStr : { () } StdIO String 
     PutCh : Char -> { () } StdIO ()
     GetCh : { () } StdIO Char

instance Handler StdIO IO where
    handle () (PutStr s) k = do putStr s; k () ()
    handle () GetStr     k = do x <- getLine; k x ()
    handle () (PutCh c)  k = do putChar c; k () () 
    handle () GetCh      k = do x <- getChar; k x ()

--- The Effect and associated functions

STDIO : EFFECT
STDIO = MkEff () StdIO

putStr : Handler StdIO e => String -> { [STDIO] } Eff e ()
putStr s = PutStr s

putChar : Handler StdIO e => Char -> { [STDIO] } Eff e ()
putChar c = PutCh c

putStrLn : Handler StdIO e => String -> { [STDIO] } Eff e ()
putStrLn s = putStr (s ++ "\n")

getStr : Handler StdIO e => { [STDIO] } Eff e String
getStr = GetStr

getChar : Handler StdIO e => { [STDIO] } Eff e Char
getChar = GetCh

