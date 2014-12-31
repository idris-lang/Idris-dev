import Data.Vect

data MyNat = MyO | MyS MyNat

%default total

data Bad = MkBad (Bad -> Int) Int
         | MkBad' Int

vapp : Vect n a -> Vect m a -> Vect (n + m) a
vapp []        ys = ys
vapp (x :: xs) ys = x :: vapp xs ys

foo : Bad -> Int
foo (MkBad f i) = f (MkBad' i)
foo (MkBad' x) = x

