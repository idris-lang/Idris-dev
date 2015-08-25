import Effects
import Effect.Logging

func : Nat -> Eff () [LOG String]
func x = do
  log WARN Nil $ unwords ["I do nothing with", show x]
  pure ()

doubleFunc : Nat -> Eff Nat [LOG String]
doubleFunc x = do
  log WARN ["NumOPS"] $ unwords ["Doing the double with", show x ]
  func x
  pure (x+x)

eMain : Eff () [LOG String]
eMain = do
  initLogger ALL ["NumOPS"]
  doubleFunc 3

main : IO ()
main = do
   x <- run eMain
   printLn x
