append : List a -> List a -> List a
append [] ys = ys
append (X :: XS) ys = X :: append XS ys
