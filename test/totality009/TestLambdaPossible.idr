||| Some functions that should be non-total, as detected with --warnpartial
module TestLambdaPossible

data Nool : Bool -> Type where
  Flase : Nool False
  Ture : Nool True

wrongPossible : Nool True -> Bool
wrongPossible = (\Flase impossible)

wrongPossible' : Nool True -> Bool
wrongPossible' x = case x of
                        Flase impossible

