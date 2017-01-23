import Data.Vect

%default total

interface ArrayM where
  Array : (n : Nat) -> (a : Type) -> Type
  create : (n : Nat) -> a -> Array n a

  lkp : (i : Nat) -> (prf : LTE (S i) n) -> Array n a -> a
  upd : a -> (i : Nat) -> (prf : LT i n) -> Array n a -> Array n a

using (ArrayM)
  sumArrayHelp : Num a => (k : Nat) -> LT k (S n) -> Array n a -> a
  sumArrayHelp Z x y = 0
  sumArrayHelp (S k) (LTESucc prf) y 
    = lkp k prf y + sumArrayHelp k (lteSuccRight prf) y

  sumArray : Array n Int -> Int
  sumArray {n} x = sumArrayHelp n lteRefl x

implementation ArrayM where
  Array = Vect 

  create n x = replicate n x

  lkp Z (LTESucc x) (y :: xs) = y
  lkp (S k) (LTESucc x) (y :: xs) = lkp k x xs

  upd val Z (LTESucc p) (_ :: xs) = val :: xs 
  upd val (S k) (LTESucc p) (x :: xs) = x :: upd val k p xs

-- using (ArrayM as vectArray)

testSum : Array n Int -> Int
testSum = sumArray 

main : IO ()
main = printLn (testSum (upd 11 1 (LTESucc (LTESucc LTEZero)) (create 4 10)))
