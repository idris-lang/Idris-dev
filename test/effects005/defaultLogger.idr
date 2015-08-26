import Effects
import Effect.Logging.Default

doubleFunc : Nat -> Eff Nat [LOG]
doubleFunc x = do
  warn $ unwords ["Doing the double with", show x ]
  pure (x+x)

main : IO ()
main = do
   x <- runInit [MkLogRes ALL] (doubleFunc 3)
   printLn x
   y <- run (doubleFunc 4)
   printLn y
