module system

import prelude

%access public

getArgs : IO (List String)
getArgs = do n <- numArgs
             ga' [] 0 n 
  where
    numArgs : IO Int
    numArgs = mkForeign (FFun "epic_numArgs" [] FInt)

    getArg : Int -> IO String
    getArg x = mkForeign (FFun "epic_getArg" [FInt] FString) x

    ga' : List String -> Int -> Int -> IO (List String)
    ga' acc i n = if (i == n) then (return $ reverse acc) else
                    do arg <- getArg i
                       ga' (arg :: acc) (i+1) n

getEnv : String -> IO String
getEnv x = mkForeign (FFun "getenv" [FString] FString) x

exit : Int -> IO ()
exit code = mkForeign (FFun "exit" [FInt] FUnit) code

