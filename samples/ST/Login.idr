import Control.ST

data Access = LoggedOut | LoggedIn
data LoginResult = OK | BadPassword

interface DataStore (m : Type -> Type) where
  data Store : Access -> Type

  connect : ST m Var [add (Store LoggedOut)]
  disconnect : (store : Var) -> ST m () [remove store (Store LoggedOut)]
  
  readSecret : (store : Var) -> ST m String [store ::: Store LoggedIn]
  login : (store : Var) ->
          ST m LoginResult [store ::: Store LoggedOut :->
                             (\res => Store (case res of
                                                  OK => LoggedIn
                                                  BadPassword => LoggedOut))]
  logout : (store : Var) ->
           ST m () [store ::: Store LoggedIn :-> Store LoggedOut]

getData : (ConsoleIO m, DataStore m) => ST m () []
getData = do st <- connect
             OK <- login st
                | BadPassword => do putStrLn "Failure"
                                    disconnect st
             secret <- readSecret st
             putStrLn ("Secret is: " ++ show secret)
             logout st
             disconnect st

-- badGet : DataStore m => ST m () []
-- badGet = do st <- connect
--             secret <- readSecret st
--             disconnect st

DataStore IO where
  Store x = State String -- represents secret data

  connect = do store <- new "Secret Data"
               pure store

  disconnect store = delete store

  readSecret store = readSecret store

  login store = do putStr "Enter password: "
                   p <- getStr
                   if p == "Mornington Crescent"
                      then pure OK
                      else pure BadPassword
  logout store = pure ()

main : IO ()
main = run getData

