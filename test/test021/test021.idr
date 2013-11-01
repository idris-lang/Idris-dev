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
                                Count :- put (!(Count :- get) + 1)
                                readAcc (str :: acc)
                        else return (reverse acc)

testFile : FileIO () ()
testFile = do open "testFile" Read
              if_valid then do putStrLn (show !readFile)
                               close
                               putStrLn (show !(Count :- get))
                 else putStrLn ("Error!")

main : IO ()
main = do ioe_run (run [(), (), Count := 0] testFile)
                  (\err => print err) (\ok => return ())


