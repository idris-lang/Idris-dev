module System

import public Data.So

%include C "unistd.h"
%default partial
%access public export

||| Retrieves a value from the environment if the given key is present,
||| otherwise it returns Nothing.
getEnv : String -> IO (Maybe String)
getEnv key = do
    str_ptr <- getEnv'
    is_nil  <- nullStr str_ptr
    if is_nil
       then pure Nothing
       else pure (Just str_ptr)
  where
    getEnv' : IO String
    getEnv' = foreign FFI_C "getenv" (String -> IO String) key

||| Sets an environment variable with a given value.
||| Returns true if the operation was successful.
setEnv : String -> String -> IO Bool
setEnv key value = do
  ok <- foreign FFI_C "setenv" (String -> String -> Int -> IO Int) key value 1
  pure (ok == 0)

||| Unsets an environment variable.
||| Returns true if the variable was able to be unset.
unsetEnv : String -> IO Bool
unsetEnv key = do
  ok <- foreign FFI_C "unsetenv" (String -> IO Int) key
  pure (ok == 0)

getEnvironment : IO (List (String, String))
getEnvironment = getAllPairs 0 []
  where
    getEnvPair : Int -> IO String
    getEnvPair i = foreign FFI_C  "getEnvPair" (Int -> IO String) i

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
         then pure $ reverse $ map splitEq acc
         else getAllPairs (n + 1) (envPair :: acc)

||| Programs can either terminate successfully, or end in a caught
||| failure.
data ExitCode : Type where
  ||| Terminate successfully.
  ExitSuccess : ExitCode
  ||| Program terminated for some prescribed reason.
  |||
  ||| @errNo A non-zero numerical value indicating failure.
  ||| @prf   Proof that the int value is non-zero.
  ExitFailure : (errNo    : Int)
             -> {auto prf : So (not $ errNo == 0)}
             -> ExitCode

||| Quit with a particular exit code
exit : Int -> IO a
exit code = believe_me $ foreign FFI_C "exit" (Int -> IO ()) code

||| Terminate the program with an `ExitCode`. This code indicates the
||| success of the program's execution, and returns the success code
||| to the program's caller.
|||
||| @code The `ExitCode` for program.
exitWith : (code : ExitCode) -> IO a
exitWith ExitSuccess         = exit 0
exitWith (ExitFailure errNo) = exit errNo

||| Exit the program indicating failure.
exitFailure : IO a
exitFailure = exitWith (ExitFailure 1)

||| Exit the program after a successful run.
exitSuccess : IO a
exitSuccess = exitWith ExitSuccess

||| Get the numbers of seconds since 1st January 1970, 00:00 UTC
time : IO Integer
time = do MkRaw t <- foreign FFI_C "idris_time" (IO (Raw Integer))
          pure t

||| Specify interval to sleep for, must be in range [0, 1000000]
usleep : (i : Int) -> { auto prf : So (i >= 0 && i <= 1000000) } -> IO ()
usleep i = foreign FFI_C "usleep" (Int -> IO ()) i

system : String -> IO Int
system cmd = foreign FFI_C "system" (String -> IO Int) cmd
