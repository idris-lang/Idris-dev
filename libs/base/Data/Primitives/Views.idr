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
         = assert_total $
             let dividend = if d < 0 then -(val `div` abs d)
                                     else val `div` d
                 remainder = abs (val - dividend * d) in
                 believe_me (DivBy {d} {div = dividend} {rem = remainder}
                                   (believe_me (Refl {x = True})))

  ||| View for recursion over Integers
  data IntegerRec : Integer -> Type where
       IntegerZ : IntegerRec 0
       IntegerSucc : IntegerRec (n - 1) -> IntegerRec n
       IntegerPred : IntegerRec ((-n) + 1) -> IntegerRec (-n)
  
  ||| Covering function for `IntegerRec`
  integerRec : (x : Integer) -> IntegerRec x
  integerRec 0 = IntegerZ
  integerRec x = if x > 0 then IntegerSucc (assert_total (integerRec (x - 1)))
                      else believe_me (IntegerPred {n=-x} 
                                (assert_total (believe_me (integerRec (x + 1)))))

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
         = assert_total $
             let dividend = if d < 0 then -(val `div` abs d)
                                     else val `div` d
                 remainder = abs (val - dividend * d) in
                 believe_me (DivBy {d} {div = dividend} {rem = remainder}
                                   (believe_me (Refl {x = True})))

  ||| View for recursion over Ints
  data IntRec : Int -> Type where
       IntZ : IntRec 0
       IntSucc : IntRec (n - 1) -> IntRec n
       IntPred : IntRec ((-n) + 1) -> IntRec (-n)
  
  ||| Covering function for `IntRec`
  intRec : (x : Int) -> IntRec x
  intRec 0 = IntZ
  intRec x = if x > 0 then IntSucc (assert_total (intRec (x - 1)))
                      else believe_me (IntPred {n=-x}
                                (assert_total (believe_me (intRec (x + 1)))))
  
