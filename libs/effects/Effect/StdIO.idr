module Effect.StdIO

import Effects
import Control.IOExcept

%access public export

-------------------------------------------------------------
-- IO effects internals
-------------------------------------------------------------

||| The internal representation of StdIO effects
data StdIO : Effect where
     PutStr : String -> sig StdIO ()
     GetStr : sig StdIO String
     PutCh : Char -> sig StdIO ()
     GetCh : sig StdIO Char


-------------------------------------------------------------
-- IO effects handlers
-------------------------------------------------------------

implementation Handler StdIO IO where
    handle () (PutStr s) k = do putStr s; k () ()
    handle () GetStr     k = do x <- getLine; k x ()
    handle () (PutCh c)  k = do putChar c; k () ()
    handle () GetCh      k = do x <- getChar; k x ()

implementation Handler StdIO (IOExcept a) where
    handle () (PutStr s) k = do ioe_lift $ putStr s; k () ()
    handle () GetStr     k = do x <- ioe_lift $ getLine; k x ()
    handle () (PutCh c)  k = do ioe_lift $ putChar c; k () ()
    handle () GetCh      k = do x <- ioe_lift $ getChar; k x ()

-------------------------------------------------------------
--- The Effect and associated functions
-------------------------------------------------------------

STDIO : EFFECT
STDIO = MkEff () StdIO

||| Write a string to standard output.
putStr : String -> Eff () [STDIO]
putStr s = call $ PutStr s

||| Write a string to standard output, terminating with a newline.
putStrLn : String -> Eff () [STDIO]
putStrLn s = putStr (s ++ "\n")

||| Write a character to standard output.
putChar : Char -> Eff () [STDIO]
putChar c = call $ PutCh c

||| Write a character to standard output, terminating with a newline.
putCharLn : Char -> Eff () [STDIO]
putCharLn c = putStrLn (singleton c)

||| Read a string from standard input.
getStr : Eff String [STDIO]
getStr = call $ GetStr

||| Read a character from standard input.
getChar : Eff Char [STDIO]
getChar = call $ GetCh

||| Given a parameter `a` 'show' `a` to standard output.
print : Show a => a -> Eff () [STDIO]
print a = putStr (show a)

||| Given a parameter `a` 'show' `a` to a standard output, terminating with a newline
printLn : Show a => a -> Eff () [STDIO]
printLn a = putStrLn (show a)
