||| Matrix operations with vector space dimensionalities enforced
||| at the type level. Uses operations from interfaces in `Control.Algebra`
||| and `Control.Algebra.VectorSpace`.
module Data.Matrix.Algebraic

import public Control.Algebra
import public Control.Algebra.VectorSpace
import public Control.Algebra.NumericImplementations

import public Data.Matrix

%access public export
%default total

infixr 2 <:>  -- vector inner product
infixr 2 ><   -- vector outer product
infixr 2 <<>> -- matrix commutator
infixr 2 >><< -- matrix anticommutator
infixl 3 <\>  -- row times a matrix
infixr 4 </>  -- matrix times a column
infixr 5 <>   -- matrix multiplication
infixr 7 \&\  -- vector tensor product
infixr 7 <&>  -- matrix tensor product

-----------------------------------------------------------------------
--               Vectors as members of algebraic interfaces
-----------------------------------------------------------------------

implementation Semigroup a => Semigroup (Vect n a) where
  (<+>)= zipWith (<+>)

implementation Monoid a => Monoid (Vect n a) where
  neutral {n} = replicate n neutral

implementation Group a => Group (Vect n a) where
  inverse = map inverse

implementation AbelianGroup a => AbelianGroup (Vect n a) where {}

implementation Ring a => Ring (Vect n a) where
  (<.>) = zipWith (<.>)

implementation RingWithUnity a => RingWithUnity (Vect n a) where
  unity {n} = replicate n unity

implementation RingWithUnity a => Module a (Vect n a) where
  (<#>) r = map (r <.>)

implementation RingWithUnity a => Module a (Vect n (Vect l a)) where
  (<#>) r = map (r <#>)
-- should be Module a b => Module a (Vect n b), but results in 'overlapping implementation'

-----------------------------------------------------------------------
--                        (Ring) Vector functions
-----------------------------------------------------------------------

||| Inner product of ring vectors
(<:>) : Ring a => Vect n a -> Vect n a -> a
(<:>) w v = foldr (<+>) neutral (zipWith (<.>) w v)

||| Tensor multiply (⊗) ring vectors
(\&\) : Ring a => Vect n a -> Vect m a -> Vect (n * m) a
(\&\) {n} {m} v w = zipWith (<.>) (oextend m v) (orep n w) where
  orep : (n : Nat) -> Vect m a -> Vect (n * m) a
  orep n v = concat $ replicate n v
  oextend : (n : Nat) -> Vect k a -> Vect (k * n) a
  oextend n w = concat $ map (replicate n) w

||| Standard basis vector with one nonzero entry, ring data type and vector-length unfixed
basis : RingWithUnity a => (Fin d) -> Vect d a
basis i = replaceAt i unity neutral

-----------------------------------------------------------------------
--                         Ring Matrix functions
-----------------------------------------------------------------------

||| Matrix times a column vector
(</>) : Ring a => Matrix n m a -> Vect m a -> Vect n a
(</>) m v = map (v <:>) m

||| Matrix times a row vector
(<\>) : Ring a => Vect n a -> Matrix n m a -> Vect m a
(<\>) r m = map (r <:>) $ transpose m

||| Matrix multiplication
(<>) : Ring a => Matrix n k a ->
                 Matrix k m a ->
                 Matrix n m a
(<>) m1 m2 = map (<\> m2) m1

||| Tensor multiply (⊗) for ring matrices
(<&>) : Ring a => Matrix h1 w1 a -> Matrix h2 w2 a -> Matrix (h1 * h2) (w1 * w2) a
(<&>) m1 m2 = zipWith (\&\) (stepOne m1 m2) (stepTwo m1 m2) where
  stepOne : Matrix h1 w1 a -> Matrix h2 w2 a -> Matrix (h1 * h2) w1 a
  stepOne {h2} m1 m2 = concat $ map (replicate h2) m1
  stepTwo : Matrix h1 w1 a -> Matrix h2 w2 a -> Matrix (h1 * h2) w2 a
  stepTwo {h1} m1 m2 = concat $ replicate h1 m2

||| Outer product between ring vectors
(><) : Ring a => Vect n a -> Vect m a -> Matrix n m a
(><) x y = col x <> row y

||| Matrix commutator
(<<>>) : Ring a => Matrix n n a -> Matrix n n a -> Matrix n n a
(<<>>) m1 m2 = (m1 <> m2) <-> (m2 <> m1)

||| Matrix anti-commutator
(>><<) : Ring a => Matrix n n a -> Matrix n n a -> Matrix n n a
(>><<) m1 m2 = (m1 <> m2) <+> (m2 <> m1)

||| Identity matrix
Id : RingWithUnity a => Matrix d d a
Id = map (\n => basis n) (fins _)

||| Square matrix from diagonal elements
diag_ : Monoid a => Vect n a -> Matrix n n a
diag_ = zipWith (\f => \x => replaceAt f x neutral) (fins _)

||| Combine two matrices to make a new matrix in block diagonal form
blockDiag : Monoid a => Matrix n n a -> Matrix m m a -> Matrix (n+m) (n+m) a
blockDiag g h = map (++ replicate _ neutral) g ++ map ((replicate _ neutral) ++) h


-----------------------------------------------------------------------
--                           Determinants
-----------------------------------------------------------------------

||| Alternating sum
altSum : Group a => Vect n a -> a
altSum (x::y::zs) = (x <-> y) <+> altSum zs
altSum [x]        = x
altSum []         = neutral

||| Determinant of a 2-by-2 matrix
det2 : Ring a => Matrix 2 2 a -> a
det2 [[x1,x2],[y1,y2]] = x1 <.> y2 <-> x2 <.> y1

||| Determinant of a square matrix
det : Ring a => Matrix (S (S n)) (S (S n)) a -> a
det {n} m = case n of
  Z     => det2 m
  (S k) => altSum . map (\c => indices FZ c m <.> det (subMatrix FZ c m))
         $ fins (S (S (S k)))

-----------------------------------------------------------------------
--                      Matrix Algebra Properties
-----------------------------------------------------------------------

-- TODO: Prove properties of matrix algebra for 'Verified' algebraic interfaces
