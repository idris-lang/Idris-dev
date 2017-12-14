module Main 

import Control.IOExcept
import Control.ST
import Control.ST.File
import Control.ST.ImplicitCall

testFile : (ConsoleIO m, File m) => ST m () []
testFile = with ST do 
              Right fileHandle <- open "writeStringTestFile" WriteTruncate
                    | Left ferr =>  do putStrLn (show ferr)
                                       pure ()
              Right _ <- writeString fileHandle "HELLO!!"
                    | Left ferr =>  do putStrLn (show ferr)
                                       close fileHandle
                                       pure ()
              Right _ <- writeString fileHandle "WORLD!!"
                    | Left ferr =>  do putStrLn (show ferr)
                                       close fileHandle
                                       pure ()
              Right _ <- writeString fileHandle "\n"
                    | Left ferr =>  do putStrLn (show ferr)
                                       close fileHandle
                                       pure ()
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
