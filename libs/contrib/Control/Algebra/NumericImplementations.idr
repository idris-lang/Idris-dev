||| Implementations of algebraic interfaces (group, ring, etc) for numeric data types,
||| and Complex number types.
module Control.Algebra.NumericImplementations

import Control.Algebra
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
