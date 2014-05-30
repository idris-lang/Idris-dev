module reg014

Matrix : Type -> Nat -> Nat -> Type
Matrix a n m = Vect n (Vect m a)

mytranspose : Matrix a (S n) (S m) -> Matrix a (S m) (S n)
mytranspose ((x:: []) :: []) = [[x]]
mytranspose [x :: y :: xs] = [x] :: (mytranspose [y :: xs])
mytranspose (x :: y :: xs)
    = let tx = mytranspose [x] in
      let ux = mytranspose (y :: xs) in zipWith (++) tx ux

