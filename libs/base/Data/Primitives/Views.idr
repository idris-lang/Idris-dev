module Data.Primitives.Views

-- We need all the believe_mes and asserts throughout this file because we're
-- working with primitive here! We also have separate implementations per
-- primitive, rather than using interfaces, because we're only going to trust
-- the primitive implementations.

namespace Integer
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

namespace Int
  ||| View for expressing a number as a multiplication + a remainder
  public export
  data Divides : Int -> (d : Int) -> Type where
       DivByZero : Int.Divides x 0
       DivBy : (prf : rem >= 0 && rem < d = True) ->
               Int.Divides ((d * div) + rem) d
   
  -- I have assumed, but not actually verified, that this will still
  -- give a right result (i.e. still adding up) when the Ints overflow.
  -- TODO: Someone please check this and fix if necessary...

  ||| Covering function for the `Divides` view
  export
  divides : (val : Int) -> (d : Int) -> Divides val d
  divides val 0 = DivByZero
  divides val d
         = let dividend = if d < 0 then -(val `div` abs d)
                                   else val `div` d
               remainder = val `mod` d in
               believe_me (DivBy {d} {div = dividend} {rem = remainder}
                                 (believe_me (Refl {x = True})))

