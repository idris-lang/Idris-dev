import Control.ST
import Control.ST.ImplicitCall

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

getData : (ConsoleIO m, DataStore m) => 
          (failcount : Var) -> ST m () [failcount ::: State Integer]
getData failcount
   = do st <- call connect
        OK <- login st
           | BadPassword => do putStrLn "Failure"
                               fc <- read failcount
                               write failcount (fc + 1)
                               putStrLn ("Number of failures: " ++ show (fc + 1))
                               disconnect st
                               getData failcount
        secret <- readSecret st
        putStrLn ("Secret is: " ++ show secret)
        logout st
        disconnect st
        getData failcount

getData2 : (ConsoleIO m, DataStore m) => 
           (st, failcount : Var) -> 
           ST m () [st ::: Store {m} LoggedOut, failcount ::: State Integer]
getData2 st failcount
   = do OK <- login st
           | BadPassword => do putStrLn "Failure"
                               fc <- read failcount
                               write failcount (fc + 1)
                               putStrLn ("Number of failures: " ++ show (fc + 1))
                               getData2 st failcount
        secret <- readSecret st
        putStrLn ("Secret is: " ++ show secret)
        logout st
        getData2 st failcount

DataStore IO where
  Store x = State String -- represents secret data

  connect = do store <- new "Secret Data"
               pure store

  disconnect store = delete store

  readSecret store = read store

  login store = do putStr "Enter password: "
                   p <- getStr
                   if p == "Mornington Crescent"
                      then pure OK
                      else pure BadPassword
  logout store = pure ()

main : IO ()
main = run (do fc <- new 0
               st <- connect
               getData2 st fc
               disconnect st
               delete fc)

