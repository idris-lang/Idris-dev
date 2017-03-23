data Rev : List a -> Type where
  RSnoc : (x : a) -> Rev xs -> Rev (xs ++ [x])
  RNil : Rev []

total
f : (x : a) -> (ys : List a) -> (rxs : Rev (ys ++ [x])) -> Void
f _ [] (RSnoc _ _) impossible -- = ?wat
f _ [] RNil impossible
f _ (_ :: _) (RSnoc _ _) impossible
f _ (_ :: _) RNil impossible

