import Effects
import Effect.Logging.Default

func : Nat -> Eff () [LOG String]
func x = do
  log WARN Nil $ unwords ["I do nothing with", show x]
  pure ()

doubleFunc : Nat -> Eff Nat [LOG String]
doubleFunc x = do
  log WARN ["NumOPS"] $ unwords ["Doing the double with", show x ]
  func x
  pure (x+x)

main : IO ()
main = do
   x <- runInit [(ALL,["NumOPS"])] (doubleFunc 3)
   printLn x
