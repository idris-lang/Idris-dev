module Main

import Solver

step : Nat -> IO ()
step n = do
  putStrLn $
    case fillBoard {n=n} emptyBoard Base of
      Just xs => ("Solved " <+> show n <+> "^2:\n" <+> show (getWitness xs))
      Nothing => ("Failed to solve " <+> show n <+> "^2")
  step (S n)

main : IO ()
main = step 0
