module Main

import System

%include C "sys.h"
%link C "sys.o"

WIFEXITED : (status : Int) -> IO Bool
WIFEXITED status = do
  r <- foreign FFI_C "WIFEXITED_" (Int -> IO Int) status
  pure $ r /= 0

WEXITSTATUS : (status : Int) -> IO Int
WEXITSTATUS status = foreign FFI_C "WEXITSTATUS_" (Int -> IO Int) status

execute : (cmd : String) -> (expectedStatus : Int) -> IO ()
execute cmd expectedStatus = do
  putStrLn "-------------------------------------------"
  putStrLn $ "Executing '" ++ cmd ++ "'"
  status1 <- system cmd
  putStrLn $ "raw status = " ++ show status1 -- XXX: Probably not portable.
  exited <- WIFEXITED status1
  if exited
    then do
      exitStatus <- WEXITSTATUS status1
      putStrLn $ "exit status = " ++ show exitStatus
      printLn $ exitStatus == expectedStatus
    else pure ()
  putStrLn ""

main : IO ()
main = do
  execute "exit 1" 1
  execute "./exit1" 1
  execute "./does-not-exist" 127
