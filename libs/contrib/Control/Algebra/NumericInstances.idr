||| Instances of algebraic classes (group, ring, etc) for numeric data types,
||| and Complex number types.
module Control.Algebra.NumericInstances

import Control.Algebra
import Control.Algebra.VectorSpace
import Data.Complex
import Data.ZZ


implementation Semigroup Integer where
  (<+>) = (+)

implementation Monoid Integer where
  neutral = 0

implementation Group Integer where
  inverse = (* -1)

implementation AbelianGroup Integer

implementation Ring Integer where
  (<.>) = (*)

implementation RingWithUnity Integer where
  unity = 1


implementation Semigroup Int where
  (<+>) = (+)

implementation Monoid Int where
  neutral = 0

implementation Group Int where
  inverse = (* -1)

implementation AbelianGroup Int

implementation Ring Int where
  (<.>) = (*)

implementation RingWithUnity Int where
  unity = 1


implementation Semigroup Double where
  (<+>) = (+)

implementation Monoid Double where
  neutral = 0

implementation Group Double where
  inverse = (* -1)

implementation AbelianGroup Double

implementation Ring Double where
  (<.>) = (*)

implementation RingWithUnity Double where
  unity = 1

implementation Field Double where
  inverseM f _ = 1 / f


implementation Semigroup Nat where
  (<+>) = (+)

implementation Monoid Nat where
  neutral = 0

implementation Semigroup ZZ where
  (<+>) = (+)

implementation Monoid ZZ where
  neutral = 0

implementation Group ZZ where
  inverse = (* -1)

implementation AbelianGroup ZZ

implementation Ring ZZ where
  (<.>) = (*)

implementation RingWithUnity ZZ where
  unity = 1


implementation Semigroup a => Semigroup (Complex a) where
  (<+>) (a :+ b) (c :+ d) = (a <+> c) :+ (b <+> d)

implementation Monoid a => Monoid (Complex a) where
  neutral = (neutral :+ neutral)

implementation Group a => Group (Complex a) where
  inverse (r :+ i) = (inverse r :+ inverse i)

implementation Ring a => AbelianGroup (Complex a) where {}

implementation Ring a => Ring (Complex a) where
  (<.>) (a :+ b) (c :+ d) = (a <.> c <-> b <.> d) :+ (a <.> d <+> b <.> c)

implementation RingWithUnity a => RingWithUnity (Complex a) where
  unity = (unity :+ neutral)

implementation RingWithUnity a => Module a (Complex a) where
  (<#>) x = map (x <.>)

implementation RingWithUnity a => InnerProductSpace a (Complex a) where
  (x :+ y) <||> z = realPart $ (x :+ inverse y) <.> z
