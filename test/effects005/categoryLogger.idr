import Effects
import Effect.Logging.Category

func : Nat -> Eff () [LOG String]
func x = do
  warn Nil $ unwords ["I do nothing with", show x]
  pure ()

doubleFunc : Nat -> Eff Nat [LOG String]
doubleFunc x = do
  logN 40 ["NumOPS"] $ unwords ["Doing the double with", show x ]
  func x
  pure (x+x)

eMain : Eff Nat [LOG String]
eMain = do
  initLogger ALL ["NumOPS"]
  doubleFunc 3

main : IO ()
main = do
   x <- run eMain
   printLn x
