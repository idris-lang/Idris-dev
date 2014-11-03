module Data.Matrix

import Data.Complex
import Data.ZZ

%default total

infixr 2 <.>  -- vector inner product
infixr 2 ><   -- vector outer product
infixr 2 <<>> -- matrix commutator
infixr 2 >><< -- matrix anticommutator
infixl 3 <\>  -- row times a matrix
infixr 4 </>  -- matrix times a column
infixr 5 <>   -- matrix multiplication 
infixr 7 \&\  -- vector tensor product
infixr 7 <&>  -- matrix tensor product

-----------------------------------------------------------------------
--               Vectors as members of algebraic classes
-----------------------------------------------------------------------

instance Semigroup a => Semigroup (Vect n a) where
  (<+>) v w = zipWith (<+>) v w

instance Monoid a => Monoid (Vect n a) where
  neutral {n} = replicate n neutral
  
instance Group a => Group (Vect n a) where
  inverse = map inverse

instance AbelianGroup a => AbelianGroup (Vect n a) where {}

instance Ring a => Ring (Vect n a) where
  (<*>) v w = zipWith (<*>) v w

instance RingWithUnity a => RingWithUnity (Vect n a) where
  unity {n} = replicate n unity

instance Field a => Field (Vect n a) where
  inverseM = map inverseM

instance RingWithUnity a => Module a (Vect n a) where
  (<#>) r v = map (r <*>) v

-----------------------------------------------------------------------
--                       (Ring) Vector functions
-----------------------------------------------------------------------

||| Inner product of ring vectors
(<.>) : Ring a => Vect n a -> Vect n a -> a
(<.>) w v = foldr (<+>) neutral (zipWith (<*>) w v)

||| Tensor multiply (⊗) ring vectors
(\&\) : Ring a => Vect n a -> Vect m a -> Vect (n * m) a
(\&\) {n} {m} v w = zipWith (<*>) (oextend m v) (orep n w) where
  orep : (n : Nat) -> Vect m a -> Vect (n * m) a
  orep n v = concat $ replicate n v
  oextend : (n : Nat) -> Vect k a -> Vect (k * n) a
  oextend n w = concat $ map (replicate n) w

||| Standard basis vector with one nonzero entry, ring data type and vector-length unfixed
basis : RingWithUnity a => {d : Nat} -> (Fin d) -> Vect d a
basis i = replaceAt i unity $ neutral


-----------------------------------------------------------------------
--                          Matrix functions
-----------------------------------------------------------------------

||| Matrix with n rows and m columns
Matrix : Nat -> Nat -> Type -> Type
Matrix n m a = Vect n (Vect m a)

||| Gets the specified column of a matrix. For rows use the vector function 'index'
getCol : Fin m -> Matrix n m a -> Vect n a
getCol fm q = map (index fm) q

||| Deletes the specified column of a matrix. For rows use the vector function 'deleteAt'
deleteCol : Fin (S m) -> Matrix n (S m) a -> Matrix n m a
deleteCol f m = map (deleteAt f) m

||| Matrix element at specified row and column indices
indices : Fin n -> Fin m -> Matrix n m a -> a
indices f1 f2 m = index f2 (index f1 m)

||| Matrix times a column vector
(</>) : Ring a => Matrix n m a -> Vect m a -> Vect n a
(</>) m v = map (v <.>) m

||| Matrix times a row vector
(<\>) : Ring a => Vect n a -> Matrix n m a -> Vect m a
(<\>) r m = map (r <.>) $ transpose m

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
  stepTwo {h1} m1 m2 = concat $ (Vect.replicate h1) m2

||| Cast a vector from a standard Vect to a proper n x 1 matrix 
col : Vect n a -> Matrix n 1 a
col v = map (\x => [x]) v

||| Cast a row from a standard Vect to a proper 1 x n matrix 
row : Vect n a -> Matrix 1 n a
row r = [r]

||| Outer product between ring vectors
(><) : Ring a => Vect n a -> Vect m a -> Matrix n m a
(><) x y = (col x) <> (row y)

||| All finite numbers up to the given bound
allN : (n : Nat) -> Vect n (Fin n)
allN Z     = Nil
allN (S n) = FZ :: (map FS $ allN n)

||| Identity matrix
Id : RingWithUnity a => {d : Nat} -> Matrix d d a
Id {d} = map (\n => basis n) $ allN d

||| Matrix commutator
(<<>>) : Ring a => Matrix n n a -> Matrix n n a -> Matrix n n a
(<<>>) m1 m2 = (m1 <> m2) <-> (m2 <> m1)

||| Matrix anti-commutator
(>><<) : Ring a => Matrix n n a -> Matrix n n a -> Matrix n n a
(>><<) m1 m2 = (m1 <> m2) <+> (m2 <> m1)


-----------------------------------------------------------------------
--                      Matrix Algebra Properties
-----------------------------------------------------------------------


-- TODO: Prove properties of matrix algebra for 'Verified' algebraic classes

-----------------------------------------------------------------------
--                    Numberic data types as rings
-----------------------------------------------------------------------

instance Semigroup Integer where
  (<+>) = (+)

instance Monoid Integer where
  neutral = 0

instance Group Integer where
  inverse = (* -1)
  
instance AbelianGroup Integer

instance Ring Integer where 
  (<*>) = (*)

instance RingWithUnity Integer where
  unity = 1


instance Semigroup Int where
  (<+>) = (+)

instance Monoid Int where
  neutral = 0

instance Group Int where
  inverse = (* -1)
  
instance AbelianGroup Int

instance Ring Int where 
  (<*>) = (*)

instance RingWithUnity Int where
  unity = 1


instance Semigroup Float where
  (<+>) = (+)

instance Monoid Float where
  neutral = 0

instance Group Float where
  inverse = (* -1)
  
instance AbelianGroup Float

instance Ring Float where 
  (<*>) = (*)

instance RingWithUnity Float where
  unity = 1

instance Field Float where
  inverseM f = 1 / f


instance Semigroup Nat where
  (<+>) = (+)

instance Monoid Nat where
  neutral = 0
  
instance VerifiedSemigroup Nat where
  semigroupOpIsAssociative = plusAssociative

instance VerifiedMonoid Nat where
  monoidNeutralIsNeutralL = plusZeroRightNeutral
  monoidNeutralIsNeutralR = plusZeroLeftNeutral


instance Semigroup ZZ where
  (<+>) = (+)

instance Monoid ZZ where
  neutral = 0

instance Group ZZ where
  inverse = (* -1)
  
instance AbelianGroup ZZ

instance Ring ZZ where 
  (<*>) = (*)
 
instance RingWithUnity ZZ where
  unity = 1


instance Semigroup a => Semigroup (Complex a) where
  (<+>) (a :+ b) (c :+ d) = (a <+> c) :+ (b <+> d)

instance Monoid a => Monoid (Complex a) where
  neutral = (neutral :+ neutral)

instance Group a => Group (Complex a) where
  inverse (r :+ i) = (inverse r :+ inverse i)

instance Ring a => AbelianGroup (Complex a) where {}

instance Ring a => Ring (Complex a) where
  (<*>) (a :+ b) (c :+ d) = (a <*> c <-> b <*> d) :+ (a <*> d <+> b <*> c)

instance RingWithUnity a => RingWithUnity (Complex a) where
  unity = (unity :+ neutral)
