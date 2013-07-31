module Main

import System.Concurrency.Process

ping : ProcID String -> ProcID String -> Process String ()
ping main proc 
   = do lift (usleep 1000)
        send proc "Hello!"
        lift (putStrLn "Sent ping")
        msg <- recv
        lift (putStrLn ("Reply: " ++ show msg))
        send main "Done"

pong : Process String ()
pong = do -- lift (putStrLn "Waiting for message")
          (sender, m) <- recvWithSender
          lift $ putStrLn ("Received " ++ m) 
          send sender ("Hello back!")

mainProc : Process String ()
mainProc = do mainID <- myID
              pongth <- create pong
              pingth <- create (ping mainID pongth)
              recv -- block until everything done
              return ()

repeatIO : Int -> UnsafeIO ()
repeatIO 0 = return ()
repeatIO n = do print n
                run mainProc 
                repeatIO (n - 1)

main : UnsafeIO ()
main = repeatIO 100

