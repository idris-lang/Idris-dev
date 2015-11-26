||| Instances of algebraic classes (group, ring, etc) for numeric data types,
||| and Complex number types.
module Control.Algebra.NumericInstances

import Control.Algebra
import Control.Algebra.VectorSpace
import Data.Complex
import Data.ZZ


instance Semigroup Integer where
  (<+>) = (+)

instance Monoid Integer where
  neutral = 0

instance Group Integer where
  inverse = (* -1)

instance AbelianGroup Integer

instance Ring Integer where
  (<.>) = (*)

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
  (<.>) = (*)

instance RingWithUnity Int where
  unity = 1


instance Semigroup Double where
  (<+>) = (+)

instance Monoid Double where
  neutral = 0

instance Group Double where
  inverse = (* -1)

instance AbelianGroup Double

instance Ring Double where
  (<.>) = (*)

instance RingWithUnity Double where
  unity = 1

instance Field Double where
  inverseM f _ = 1 / f


instance Semigroup Nat where
  (<+>) = (+)

instance Monoid Nat where
  neutral = 0

instance Semigroup ZZ where
  (<+>) = (+)

instance Monoid ZZ where
  neutral = 0

instance Group ZZ where
  inverse = (* -1)

instance AbelianGroup ZZ

instance Ring ZZ where
  (<.>) = (*)

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
  (<.>) (a :+ b) (c :+ d) = (a <.> c <-> b <.> d) :+ (a <.> d <+> b <.> c)

instance RingWithUnity a => RingWithUnity (Complex a) where
  unity = (unity :+ neutral)

instance RingWithUnity a => Module a (Complex a) where
  (<#>) x = map (x <.>)

instance RingWithUnity a => InnerProductSpace a (Complex a) where
  (x :+ y) <||> z = realPart $ (x :+ inverse y) <.> z
