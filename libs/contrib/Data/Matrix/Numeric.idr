||| Matrix operations with vector space dimensionalities enforced
||| at the type level. Uses operations from the Num interface.
module Data.Matrix.Numeric

import public Data.Matrix

%default total
%access public export

infixr 2 <:>  -- vector inner product
infixr 2 ><   -- vector outer product
infixr 2 <<>> -- matrix commutator
infixr 2 >><< -- matrix anticommutator
infixl 3 <\>  -- row times a matrix
infixr 4 </>  -- matrix times a column
infixr 5 <>   -- matrix multiplication
infixl 5 <#>  -- matrix rescale
infixl 5 <#   -- vector rescale
infixr 7 \&\  -- vector tensor product
infixr 7 <&>  -- matrix tensor product

-----------------------------------------------------------------------
--                   Vectors as members of Num
-----------------------------------------------------------------------

implementation Num a => Num (Vect n a) where
  (+) = zipWith (+)
  (*) = zipWith (*)
  fromInteger n = replicate _ (fromInteger n)

implementation Neg a => Neg (Vect n a) where
  (-) = zipWith (-)
  abs = map abs
  negate = map negate

-----------------------------------------------------------------------
--                        Vector functions
-----------------------------------------------------------------------

||| Inner product of ring vectors
(<:>) : Num a => Vect n a -> Vect n a -> a
(<:>) w v = sum $ zipWith (*) w v

||| Scale a numeric vector by a scalar
(<#) : Num a => a -> Vect n a -> Vect n a
(<#) r = map (r *)

||| Tensor multiply (⊗) numeric vectors
(\&\) : Num a => Vect n a -> Vect m a -> Vect (n * m) a
(\&\) {n} {m} v w = zipWith (*) (oextend m v) (orep n w) where
  orep : (n : Nat) -> Vect m a -> Vect (n * m) a
  orep n v = concat $ replicate n v
  oextend : (n : Nat) -> Vect k a -> Vect (k * n) a
  oextend n w = concat $ map (replicate n) w

||| Standard basis vector with one nonzero entry, numeric data type and vector-length unfixed
basis : Num a => (Fin d) -> Vect d a
basis i = replaceAt i 1 0

-----------------------------------------------------------------------
--                          Matrix functions
-----------------------------------------------------------------------

||| Matrix times a column vector
(</>) : Num a => Matrix n m a -> Vect m a -> Vect n a
(</>) m v = map (v <:>) m

||| Matrix times a row vector
(<\>) : Num a => Vect n a -> Matrix n m a -> Vect m a
(<\>) r m = map (r <:>) $ transpose m

||| Matrix multiplication
(<>) : Num a => Matrix n k a ->
                Matrix k m a ->
                Matrix n m a
(<>) m1 m2 = map (<\> m2) m1

||| Scale matrix by a scalar
(<#>) : Num a => a -> Matrix n m a -> Matrix n m a
(<#>) r = map (r <#)

||| Tensor multiply (⊗) for numeric matrices
(<&>) : Num a => Matrix h1 w1 a -> Matrix h2 w2 a -> Matrix (h1 * h2) (w1 * w2) a
(<&>) m1 m2 = zipWith (\&\) (stepOne m1 m2) (stepTwo m1 m2) where
  stepOne : Matrix h1 w1 a -> Matrix h2 w2 a -> Matrix (h1 * h2) w1 a
  stepOne {h2} m1 m2 = concat $ map (replicate h2) m1
  stepTwo : Matrix h1 w1 a -> Matrix h2 w2 a -> Matrix (h1 * h2) w2 a
  stepTwo {h1} m1 m2 = concat $ replicate h1 m2

||| Outer product between numeric vectors
(><) : Num a => Vect n a -> Vect m a -> Matrix n m a
(><) x y = col x <> row y

||| Matrix commutator
(<<>>) : Neg a => Matrix n n a -> Matrix n n a -> Matrix n n a
(<<>>) m1 m2 = (m1 <> m2) - (m2 <> m1)

||| Matrix anti-commutator
(>><<) : Num a => Matrix n n a -> Matrix n n a -> Matrix n n a
(>><<) m1 m2 = (m1 <> m2) + (m2 <> m1)

||| Identity matrix
Id : Num a => Matrix d d a
Id = map (\n => basis n) (fins _)

||| Square matrix from diagonal elements
diag_ : Num a => Vect n a -> Matrix n n a
diag_ = zipWith (\f => \x => replaceAt f x 0) (fins _)

||| Combine two matrices to make a new matrix in block diagonal form
blockDiag : Num a => Matrix n n a -> Matrix m m a -> Matrix (n+m) (n+m) a
blockDiag {n} {m} g h = map (++ replicate m 0) g ++ map ((replicate n 0) ++) h

-----------------------------------------------------------------------
--                           Determinants
-----------------------------------------------------------------------

||| Alternating sum
altSum : Neg a => Vect n a -> a
altSum (x::y::zs) = (x - y) + altSum zs
altSum [x]        = x
altSum []         = 0

||| Determinant of a 2-by-2 matrix
det2 : Neg a => Matrix 2 2 a -> a
det2 [[x1,x2],[y1,y2]] = x1*y2 - x2*y1

||| Determinant of a square matrix
det : Neg a => Matrix (S (S n)) (S (S n)) a -> a
det {n} m = case n of
  Z     => det2 m
  (S k) => altSum . map (\c => indices FZ c m * det (subMatrix FZ c m))
         $ fins (S (S (S k)))
