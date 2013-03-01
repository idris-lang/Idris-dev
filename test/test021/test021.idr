module Main 

import Effect.File
import Effect.State
import Effect.StdIO
import Control.IOExcept

data FName = Count | NotCount

FileIO : Type -> Type -> Type
FileIO st t 
   = Eff (IOExcept String) [FILE_IO st, STDIO, Count ::: STATE Int] t

readFile : FileIO (OpenFile Read) (List String)
readFile = readAcc [] where
    readAcc : List String -> FileIO (OpenFile Read) (List String) 
    readAcc acc = do e <- eof
                     if (not e) 
                        then do str <- readLine
                                ls <- Count :- get
                                Count :- put (ls + 1)
                                readAcc (str :: acc)
                        else return (reverse acc)

testFile : FileIO () () 
testFile = catch (do open "testFile" Read
                     str <- readFile
                     putStrLn (show str)
                     ls <- Count :- get
                     close
                     putStrLn (show ls))
                 (\err => putStrLn ("Handled: " ++ show err))

main : IO ()
main = do ioe_run (run [(), (), Count := 0] testFile)
                  (\err => print err) (\ok => return ())


