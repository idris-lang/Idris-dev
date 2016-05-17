module Data.Nat.Views

||| View for expressing a number as a multiplication + a remainder
public export
data Divides : Integer -> (d : Integer) -> Type where
     DivByZero : Divides x 0
     DivBy : (prf : rem >= 0 && rem < d = True) ->
             Divides ((d * div) + rem) d
  
||| Covering function for the `Divides` view
export
divides : (val : Integer) -> (d : Integer) -> Divides val d
divides val 0 = DivByZero
divides val d
       = let dividend = if d < 0 then -(val `div` abs d)
                                 else val `div` d
             remainder = val `mod` d in
             believe_me (DivBy {d} {div = dividend} {rem = remainder}
                               (believe_me (Refl {x = True})))
