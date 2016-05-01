||| Some functions that should be non-total
module TestLambdaPossible

data Nool : Bool -> Type where
  Flase : Nool False
  Ture : Nool True

total
wrongPossible : Nool True -> Bool
wrongPossible = (\Flase impossible)

total
wrongPossible' : Nool True -> Bool
wrongPossible' x = case x of
                        Flase impossible

