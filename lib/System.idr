module System

import Prelude

%default partial
%access public

getArgs : IO (List String)
getArgs = do n <- numArgs
             ga' [] 0 n 
  where
    numArgs : IO Int
    numArgs = mkForeign (FFun "idris_numArgs" [FPtr] FInt) prim__vm

    getArg : Int -> IO String
    getArg x = mkForeign (FFun "idris_getArg" [FPtr, FInt] (FAny String)) prim__vm x

    ga' : List String -> Int -> Int -> IO (List String)
    ga' acc i n = if (i == n) then (return $ reverse acc) else
                    do arg <- getArg i
                       ga' (arg :: acc) (i+1) n

getEnv : String -> IO (Maybe String)
getEnv key = do 
    str_ptr <- getEnv'
    exists  <- nullStr str_ptr
    if exists
       then pure Nothing
       else pure (Just str_ptr)
  where
    getEnv' : IO String
    getEnv' = mkForeign (FFun "getenv" [FString] FString) key

exit : Int -> IO ()
exit code = mkForeign (FFun "exit" [FInt] FUnit) code

usleep : Int -> IO ()
usleep i = mkForeign (FFun "usleep" [FInt] FUnit) i

