||| Implementations of algebraic interfaces (group, ring, etc) for numeric data types,
||| and Complex number types.
module Control.Algebra.NumericImplementations

import Control.Algebra
import Control.Algebra.VectorSpace
import Data.Complex
import Data.ZZ

%access public export

-- Integer

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

-- Int

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

-- Double

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

-- Nat

[PlusNatSemi] Semigroup Nat where
  (<+>) = (+)

[PlusNatMonoid] Monoid Nat using PlusNatSemi where
  neutral = 0

[MultNatSemi] Semigroup Nat where
  (<+>) = (*)

[MultNatMonoid] Monoid Nat using MultNatSemi where
  neutral = 1

-- ZZ

[PlusZZSemi] Semigroup ZZ where
  (<+>) = (+)

[PlusZZMonoid] Monoid ZZ using PlusZZSemi where
  neutral = 0

Group ZZ using PlusZZMonoid where
  inverse = (* -1)

AbelianGroup ZZ where

[MultZZSemi] Semigroup ZZ where
  (<+>) = (*)

[MultZZMonoid] Monoid ZZ using MultZZSemi where
  neutral = 1

Ring ZZ where
  (<.>) = (*)

RingWithUnity ZZ where
  unity = 1

-- Complex

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
