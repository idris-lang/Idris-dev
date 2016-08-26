module Main

import Resimp

data Purpose = Reading | Writing

pstring : Purpose -> String
pstring Reading = "r"
pstring Writing = "w"

data FILE : Purpose -> Type where
    OpenH : File -> FILE p

syntax "ifM" [test] "then" [t] "else" [e]
    = test >>= (\b => if b then t else e)

open : String -> (p:Purpose) -> Creator (Either () (FILE p))
open fn p = ioc (do Right h <- fopen fn (pstring p)
                       | Left err => pure (Left ())
                    pure (Right (OpenH h)))

close : FILE p -> Updater ()
close (OpenH h) = iou (closeFile h)

readLine : FILE Reading -> Reader String
readLine (OpenH h) = ior (do Right str <- fGetLine h
                                   | pure ""
                             pure str)

eof : FILE Reading -> Reader Bool
eof (OpenH h) = ior (fEOF h)

syntax rclose [h]    = Update close h
syntax rreadLine [h] = Use readLine h
syntax reof [h]      = Use eof h

syntax rputStrLn [s] = Lift (putStrLn s)
syntax rputStr [s] = Lift (putStr s)

syntax "if" "opened" [f] "then" [e] "else" [t] = Check f t e















--------

readH : String -> RES ()
readH fn = res (do let x = open fn Reading
                   if opened x then
                       do str <- rreadLine x
                          rputStr str
                          rclose x
                       else rputStrLn "Error")

main : IO ()
main = run (readH "test")


