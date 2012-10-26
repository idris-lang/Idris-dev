module scg

total
vtrans : Vect a n -> Vect a n -> List a
vtrans [] _         = []
vtrans (x :: xs) ys = x :: vtrans ys ys

