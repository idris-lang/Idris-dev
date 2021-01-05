module Data.Sign

import Prelude.Algebra

%access public export

%default total

||| A representation of signs for signed datatypes such as `ZZ`
data Sign = Plus | Zero | Minus

-- Signed interface --------------------

||| Discover the sign of some type
interface Signed t where
  total sign : t -> Sign

Signed Int where
  sign x with (compare x 0)
    | LT = Minus
    | EQ = Zero
    | GT = Plus

Signed Integer where
  sign x with (compare x 0)
    | LT = Minus
    | EQ = Zero
    | GT = Plus

Signed Double where
  sign x with (compare x 0.0)
    | LT = Minus
    | EQ = Zero
    | GT = Plus

-- Implementations ---------------------

Eq Sign where
  Zero == Zero = True
  Plus == Plus = True
  Minus == Minus = True
  _ == _ = False

Num Sign where
  (+) Zero x      = x
  (+) x Zero      = x
  (+) Plus Minus  = Zero
  (+) Plus Plus   = Plus
  (+) Minus Plus  = Zero
  (+) Minus Minus = Minus

  (*) Zero  _     = Zero
  (*) _     Zero  = Zero
  (*) Plus  x     = x
  (*) x     Plus  = x
  (*) Minus Minus = Plus

  fromInteger 0 = Zero
  fromInteger n = if n > 0 then Plus else Minus

Neg Sign where
  negate Plus  = Minus
  negate Zero  = Zero
  negate Minus = Plus

  (-) x y = x + negate y

Abs Sign where
  abs Zero = Zero
  abs _    = Plus

Ord Sign where
  compare Zero Zero   = EQ
  compare Plus Plus   = EQ
  compare _ Plus      = LT
  compare Plus _      = GT
  compare Minus Minus = EQ
  compare Minus _     = LT
  compare _ Minus     = GT

MinBound Sign where
  minBound = Minus

MaxBound Sign where
  maxBound = Plus

-- Algebra -----------------------------

Semigroup Sign where
  (<+>) = (*)

Monoid Sign where
  neutral = Plus
