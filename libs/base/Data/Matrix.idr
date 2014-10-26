module Data.Matrix

import Data.Complex

%default total

infixl 1 \+\  -- Vector plus  (mnemonic: V begins with '\'
infixl 1 /+/  -- Matrix plus             M begins with '/')
infixl 1 \-\  -- Vector minus
infixl 1 /-/  -- Matrix minus
infixr 2 <.>  -- Vector inner product
infixr 2 ><   -- Vector outer product
infixr 2 <<>> -- Matrix commutator
infixr 2 >><< -- Matrix anticommutator
infixl 3 <\>  -- row times a matrix
infixr 4 </>  -- matrix times a column
infixr 5 <>   -- matrix multiplication 
infixr 7 \&\  -- vector tensor product
infixr 7 <&>  -- matrix tensor product

-----------------------------------------------------------------------
--                          Vector Stuff
-----------------------------------------------------------------------

||| Inner product of ring vectors
(<.>) : Ring a => Vect n a -> Vect n a -> a
(<.>) w v = foldr (<+>) neutral (zipWith (<*>) w v)

||| Scale a ring vector by the appropriate scalar
scale : Ring a => a -> Vect n a -> Vect n a
scale s v = map (<*> s) v

||| Vector addition
(\+\) : Ring a => Vect n a -> Vect n a -> Vect n a
(\+\) v w = zipWith (<+>) v w

||| Vector subtraction
(\-\) : Ring a => Vect n a -> Vect n a -> Vect n a
(\-\) v w = zipWith (<->) v w

||| Tensor multiply (⊗) ring vectors
(\&\) : Ring a => Vect n a -> Vect m a -> Vect (n * m) a
(\&\) {n} {m} v w = zipWith (<*>) (oextend m v) (orep n w) where
  orep : (n : Nat) -> Vect m a -> Vect (n * m) a
  orep n v = concat $ replicate n v
  oextend : (n : Nat) -> Vect k a -> Vect (k * n) a
  oextend n w = concat $ map (replicate n) w

||| Zero vector
zero : Monoid a => {d : Nat} -> Vect d a
zero {d} = replicate d neutral

||| Standard basis vector with one nonzero entry, ring data type and vector-length unfixed
basis : RingWithUnity a => {d : Nat} -> (Fin d) -> Vect d a
basis i = replaceAt i unity $ zero

||| All-unit vector
flat : RingWithUnity a => {d : Nat} -> Vect d a
flat {d} = replicate d unity


-----------------------------------------------------------------------
--                          Matrix Stuff
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

||| Matrix addition
(/+/) : Ring a => Matrix n m a -> Matrix n m a -> Matrix n m a
(/+/) = zipWith (\+\)

||| Matrix subtraction
(/-/) : Ring a => Matrix n m a -> Matrix n m a -> Matrix n m a
(/-/) = zipWith (\-\)

||| Ring scalar times a matrix
RescaleBy.(*) : Ring a => a -> Matrix n m a -> Matrix n m a
RescaleBy.(*) s m = map (map (s <*>)) m

||| Rescale matrix by a ring scalar
RescaleMatrix.(*) : Ring a => Matrix n m a -> a -> Matrix n m a
RescaleMatrix.(*) m s = map (map (<*> s)) m 

||| Matrix times a column vector
(</>) : Ring a => Matrix n m a -> Vect m a -> Vect n a
(</>) m v = map (v <.>) m

||| Matrix times a row vector
(<\>) : Ring a => Vect n a -> Matrix n m a -> Vect m a
(<\>) r m = map (r <.>) $ transpose m

||| Matrix Multiplication
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

||| Zero matrix
Zero : Monoid a => {d : Nat} -> Matrix d d a
Zero {d} = replicate d zero

||| Matrix Commutator
(<<>>) : Ring a => Matrix n n a -> Matrix n n a -> Matrix n n a
(<<>>) m1 m2 = (m1 <> m2) /-/ (m2 <> m1)

||| Matrix Anti-Commutator
(>><<) : Ring a => Matrix n n a -> Matrix n n a -> Matrix n n a
(>><<) m1 m2 = (m1 <> m2) /+/ (m2 <> m1)


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
  

instance Semigroup a => Semigroup (Complex a) where
  (<+>) (a :+ b) (c :+ d) = (a <+> c) :+ (b <+> d)

instance (Num a, Monoid a) => Monoid (Complex a) where
  neutral = (0 :+ 0)

instance (Num a, Neg a, Group a) => Group (Complex a) where
  inverse = (\(r :+ i) => -r :+ -i)

instance Group (Complex a) => AbelianGroup (Complex a) where {}

instance (Num a, AbelianGroup (Complex a)) => Ring (Complex a) where
  (<*>) (a :+ b) (c :+ d) = (a*c - b*d) :+ (a*d + b*c)

instance (Num a, Ring (Complex a)) => RingWithUnity (Complex a) where
  unity = (1 :+ 0)


instance Semigroup Nat where
  (<+>) = (+)

instance Monoid Nat where
  neutral = 0
  
instance VerifiedSemigroup Nat where
  semigroupOpIsAssociative = plusAssociative

instance VerifiedMonoid Nat where
  monoidNeutralIsNeutralL = plusZeroRightNeutral
  monoidNeutralIsNeutralR = plusZeroLeftNeutral
