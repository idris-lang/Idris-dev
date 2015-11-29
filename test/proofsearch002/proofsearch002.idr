import Process

import Data.Vect

data Counter : Type -> Type where
     GetIdle : Counter Int
     Append : Vect n a -> Vect m a -> Counter $ Vect (n + m) a

data Maths : Type -> Type where
     Factorial : Nat -> Maths Nat

count_process : Int -> Counter t -> Response (t, Int) Counter [] p
count_process x GetIdle = Pure (x, x)
count_process x (Append xs ys) = Pure (xs ++ ys, x)

countServer : Int -> Running () Counter
countServer secs = do s' <- TimeoutRespond 1 (secs + 1) (count_process secs) 
                      Loop (countServer s')

mathsServer : Running () Maths
mathsServer = do Lift $ putStrLn "Serving maths!"
                 TimeoutRespond 5 () (\val => case val of
                                                   Factorial k => 
                                                        Pure (fact k, ()))
                 Loop mathsServer

-- Start up a couple of servers, send them requests
testProg1 : Program () (const Void)
testProg1 = do -- with Process do 
               mpid <- Fork mathsServer
               cpid <- Fork (countServer 0)
               putStr "Number1: "
               x1 <- getLine
               putStr "Number2: "
               x2 <- getLine
 
               fac1h <- Request mpid (Factorial (cast (trim x1)))
               fac2h <- Request mpid (Factorial (cast (trim x2)))

               fac2 <- GetReply fac2h -- {pending = PendingHere}
               fac1 <- GetReply fac1h -- {pending = PendingHere}

               Disconnect cpid
               Disconnect mpid

main : IO ()
main = run testProg1

