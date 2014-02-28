module System

import Prelude

%default partial
%access public

getArgs : IO (List String)
getArgs = do n <- numArgs
             ga' [] 0 n
  where
    numArgs : IO Int
    numArgs = mkForeign (FFun "idris_numArgs" [] FInt)

    getArg : Int -> IO String
    getArg x = mkForeign (FFun "idris_getArg" [FInt] FString) x

    ga' : List String -> Int -> Int -> IO (List String)
    ga' acc i n = if (i == n) then (return $ reverse acc) else
                    do arg <- getArg i
                       ga' (arg :: acc) (i+1) n

-- Retrieves an value from the environment, if the given key is present,
-- otherwise it returns Nothing.
getEnv : String -> IO (Maybe String)
getEnv key = do
    str_ptr <- getEnv'
    is_nil  <- nullStr str_ptr
    if is_nil
       then pure Nothing
       else pure (Just str_ptr)
  where
    getEnv' : IO String
    getEnv' = mkForeign (FFun "getenv" [FString] FString) key

-- Sets an environment variable with a given value.
-- Returns true if the operation was successful.
setEnv : String -> String -> IO Bool
setEnv key value = do
  ok <- mkForeign (FFun "setenv" [FString, FString, FInt] FInt) key value 1
  return (ok == 0)

-- Unsets an environment variable.
-- Returns true if the variable was able to be unset.
unsetEnv : String -> IO Bool
unsetEnv key = do
  ok <- mkForeign (FFun "unsetenv" [FString] FInt) key
  return (ok == 0)

getEnvironment : IO (List (String, String))
getEnvironment = getAllPairs 0 []
  where
    getEnvPair : Int -> IO String
    getEnvPair i = mkForeign (FFun "getEnvPair" [FInt] FString) i

    splitEq : String -> (String, String)
    splitEq str =
      -- FIXME: There has to be a better way to split this up
      let (k, v)  = break (== '=') str in
      let (_, v') = break (/= '=') v in
      (k, v')

    getAllPairs : Int -> List String -> IO (List (String, String))
    getAllPairs n acc = do
      envPair <- getEnvPair n
      is_nil  <- nullStr envPair
      if is_nil
         then return $ reverse $ map splitEq acc
         else getAllPairs (n + 1) (envPair :: acc)

exit : Int -> IO ()
exit code = mkForeign (FFun "exit" [FInt] FUnit) code

time : IO Int
time = mkForeign (FFun "idris_time" [] FInt)

usleep : Int -> IO ()
usleep i = mkForeign (FFun "usleep" [FInt] FUnit) i

