module Main

import Effects
import Effect.File
import Effect.State
import Effect.StdIO
import Control.IOExcept

data Count : Type where


TestFileIO : Type -> Type -> Type
TestFileIO st t = Eff t [FILE st, STDIO, Count ::: STATE Int]

readFileCount : Eff (FileOpResult (List String)) [FILE R, STDIO, Count ::: STATE Int]
readFileCount = readAcc []
  where
    readAcc : List String
           -> Eff (FileOpResult (List String)) [FILE R, STDIO, Count ::: STATE Int]
    readAcc acc = do
      e <- eof
      if (not e)
         then do
           (Result str) <- readLine
                         | (FError err) => pure (FError err)
           Count :- put (!(Count :- get) + 1)
           readAcc (str :: acc)
         else do
           let res = reverse acc
           pure $ Result res

testFile : TestFileIO () ()
testFile = do
    Success <- open "testFile" Read
             | (FError err) => do
                 putStrLn "Error!"
                 pure ()
    (Result fcontents) <- readFileCount
                        | (FError err) => do
                            close
                            putStrLn "Error!"
                            pure ()
    putStrLn (show fcontents)
    close
    putStrLn (show !(Count :- get))

main : IO ()
main = run testFile
