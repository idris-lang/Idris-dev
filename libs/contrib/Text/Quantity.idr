module Text.Quantity

%access public export
%default total

record Quantity where
  constructor Qty
  min : Nat
  max : Maybe Nat

Show Quantity where
  show (Qty Z Nothing) = "*"
  show (Qty Z (Just (S Z))) = "?"
  show (Qty (S Z) Nothing) = "+"
  show (Qty min max) = "{" ++ show min ++ showMax ++ "}"
    where
      showMax : String
      showMax = case max of
                     Nothing => ","
                     Just max' => if min == max'
                                     then ""
                                     else "," ++ show max'

between : Nat -> Nat -> Quantity
between min max = Qty min (Just max)

atLeast : Nat -> Quantity
atLeast min = Qty min Nothing

atMost : Nat -> Quantity
atMost max = Qty 0 (Just max)

exactly : Nat -> Quantity
exactly n = Qty n (Just n)

inOrder : Quantity -> Bool
inOrder (Qty min Nothing) = True
inOrder (Qty min (Just max)) = min <= max
