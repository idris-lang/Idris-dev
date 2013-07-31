module System

import Prelude

%default partial
%access public

getArgs : UnsafeIO (List String)
getArgs = do n <- numArgs
             ga' [] 0 n 
  where
    numArgs : UnsafeIO Int
    numArgs = mkForeign (FFun "idris_numArgs" [FPtr] FInt) prim__vm

    getArg : Int -> UnsafeIO String
    getArg x = mkForeign (FFun "idris_getArg" [FPtr, FInt] (FAny String)) prim__vm x

    ga' : List String -> Int -> Int -> UnsafeIO (List String)
    ga' acc i n = if (i == n) then (return $ reverse acc) else
                    do arg <- getArg i
                       ga' (arg :: acc) (i+1) n

getEnv : String -> UnsafeIO String
getEnv x = mkForeign (FFun "getenv" [FString] FString) x

exit : Int -> UnsafeIO ()
exit code = mkForeign (FFun "exit" [FInt] FUnit) code

usleep : Int -> UnsafeIO ()
usleep i = mkForeign (FFun "usleep" [FInt] FUnit) i

