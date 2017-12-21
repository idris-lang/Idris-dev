module Main 

import Control.IOExcept
import Control.ST
import Control.ST.File
import Control.ST.ImplicitCall

increment : (x : Var) -> STrans m () [ x ::: State Int ]
                                     (const [x ::: State Int])
increment x = do num <- read x
                 write x (num + 1)

readFileCount : (ConsoleIO m, File m) => 
                   (fileHandle : Var) 
                -> (count : Var)
                -> {auto prf   : ValidModeRead mode} 
                -> ST m (Either FileError (List String)) 
                      [ count      ::: (State Int), 
                        fileHandle ::: FileHandleI {m} mode ]
readFileCount fh cnt = 
     readAcc fh cnt []  
     where
          readAcc : (ConsoleIO m, File m) => 
                       (fileHandle : Var) 
                    -> (count : Var)
                    -> List String 
                    -> {auto prf   : ValidModeRead mode} 
                    -> ST m (Either FileError (List String)) 
                          [ count      ::: (State Int), 
                            fileHandle ::: FileHandleI {m} mode ]
          readAcc fileHandle cnt acc = with ST do 
            e <- (eof fileHandle)
            if (not e) 
               then do Right str <- (readLine fileHandle)
                             | Left ferr => pure (Left ferr)
                       (increment cnt) 
                       readAcc fileHandle cnt (str :: acc)
               else do let rev = reverse acc
                       pure (Right rev)

testFile : (ConsoleIO m, File m) => ST m () []
testFile = with ST do 
              Right fileHandle <- open "testFile" Read 
                    | Left ferr => do putStrLn (show ferr)
                                      pure ()
              count <- new 0
              Right fContents <- readFileCount fileHandle count 
                    | Left ferr => do putStrLn (show ferr)
                                      delete count
                                      close fileHandle
                                      pure ()
              putStrLn (show fContents) 
              putStrLn (show !(read count))
              delete count
              close fileHandle
              pure ()

main : IO ()
main = do putStrLn "--test IO:" 
          run testFile
          putStrLn "--test IOExcept:" 
          ioe_run (run testFile)
                  (\err => putStrLn err) 
                  (\ok  => printLn ok)

-- EOF -------------------------------------------------------------------------
