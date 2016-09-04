||| Implementations of algebraic interfaces (group, ring, etc) for numeric data types,
||| and Complex number types.
module Control.Algebra.NumericImplementations

import Control.Algebra
import Control.Algebra.VectorSpace
import Data.Complex
import Data.ZZ

%access public export

Semigroup Integer where
  (<+>) = (+)

Monoid Integer where
  neutral = 0

Group Integer where
  inverse = (* -1)

AbelianGroup Integer where 

Ring Integer where
  (<.>) = (*)

RingWithUnity Integer where
  unity = 1


Semigroup Int where
  (<+>) = (+)

Monoid Int where
  neutral = 0

Group Int where
  inverse = (* -1)

AbelianGroup Int where

Ring Int where
  (<.>) = (*)

RingWithUnity Int where
  unity = 1


Semigroup Double where
  (<+>) = (+)

Monoid Double where
  neutral = 0

Group Double where
  inverse = (* -1)

AbelianGroup Double where

Ring Double where
  (<.>) = (*)

RingWithUnity Double where
  unity = 1

Field Double where
  inverseM f _ = 1 / f


Semigroup Nat where
  (<+>) = (+)

Monoid Nat where
  neutral = 0

Semigroup ZZ where
  (<+>) = (+)

Monoid ZZ where
  neutral = 0

Group ZZ where
  inverse = (* -1)

AbelianGroup ZZ where

Ring ZZ where
  (<.>) = (*)

RingWithUnity ZZ where
  unity = 1


Semigroup a => Semigroup (Complex a) where
  (<+>) (a :+ b) (c :+ d) = (a <+> c) :+ (b <+> d)

Monoid a => Monoid (Complex a) where
  neutral = (neutral :+ neutral)

Group a => Group (Complex a) where
  inverse (r :+ i) = (inverse r :+ inverse i)

Ring a => AbelianGroup (Complex a) where {}

Ring a => Ring (Complex a) where
  (<.>) (a :+ b) (c :+ d) = (a <.> c <-> b <.> d) :+ (a <.> d <+> b <.> c)

RingWithUnity a => RingWithUnity (Complex a) where
  unity = (unity :+ neutral)

RingWithUnity a => Module a (Complex a) where
  (<#>) x = map (x <.>)

RingWithUnity a => InnerProductSpace a (Complex a) where
  (x :+ y) <||> z = realPart $ (x :+ inverse y) <.> z
