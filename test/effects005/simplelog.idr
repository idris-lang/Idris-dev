import Effects
import Effect.Logging.Simple

doubleFunc : Nat -> Eff Nat [LOG]
doubleFunc x = do
  log 3 $ unwords ["Doing the double with", show x ]
  pure (x+x)

main : IO ()
main = do
   x <- runInit [7] (doubleFunc 3)
   printLn x
   y <- runInit [0] (doubleFunc 4)
   printLn y
