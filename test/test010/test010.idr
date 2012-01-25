data MyNat = MyO | MyS MyNat

data Bad = MkBad (Bad -> Int) Int
         | MkBad' Int

total
vapp : Vect a n -> Vect a m -> Vect a (n + m)
vapp []        ys = ys
vapp (x :: xs) ys = x :: vapp xs ys

total 
foo : Bad -> Int
foo (MkBad f i) = f (MkBad' i)
foo (MkBad' x) = x
