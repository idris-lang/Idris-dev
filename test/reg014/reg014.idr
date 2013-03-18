module reg014

Matrix : Type -> Nat -> Nat -> Type
Matrix a n m = Vect (Vect a m) n

transpose : Matrix a (S n) (S m) -> Matrix a (S m) (S n)
transpose ((x:: []) :: []) = [[x]]
transpose [x :: y :: xs] = [x] :: (transpose [y :: xs])
transpose (x :: y :: xs) 
    = let tx = transpose [x] in 
      let ux = transpose (y :: xs) in zipWith (++) tx ux

