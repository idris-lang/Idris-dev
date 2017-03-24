import Network.Socket
import Network
import Control.ST
import Control.ST.ImplicitCall

echoServer : (ConsoleIO m, Sockets m) => (sock : Var) -> 
             ST m () [remove sock (Sock {m} Listening)]
echoServer sock = 
  do Right new <- accept sock | Left err => do close sock; remove sock
     Right msg <- recv new | Left err => do close sock; remove sock; remove new
     Right ok <- send new ("You said " ++ msg)
           | Left err => do remove new; close sock; remove sock
     close new; remove new; echoServer sock

startServer : (ConsoleIO m, Sockets m) => ST m () [] 
startServer = 
  do Right sock <- socket Stream        | Left err => pure () 
     Right ok <- bind sock Nothing 9442 | Left err => remove sock
     Right ok <- listen sock            | Left err => remove sock
     echoServer sock

main : IO ()
main = run startServer

