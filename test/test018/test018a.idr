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
          (sender, msg) <- recvWithSender
          lift $ putStrLn ("Received " ++ msg) 
          send sender ("Hello back!")

mainProc : Process String ()
mainProc = do mainID <- myID
              pongth <- create pong
              pingth <- create (ping mainID pongth)
              recv -- block until everything done
              return ()

repeatIO : Int -> IO ()
repeatIO 0 = return ()
repeatIO n = do print n
                run mainProc 
                repeatIO (n - 1)

main : IO ()
main = repeatIO 100

