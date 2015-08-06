import Effects
import Effect.Logging.Simple

doubleFunc : Nat -> Eff Nat [LOG]
doubleFunc x = do
  log WARN $ unwords ["Doing the double with", show x ]
  pure (x+x)

main : IO ()
main = do
   x <- runInit [ALL] (doubleFunc 3)
   printLn x
   y <- runInit [OFF] (doubleFunc 4)
   printLn y
