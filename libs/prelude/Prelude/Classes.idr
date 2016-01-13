module Prelude.Classes

import Builtins
import Prelude.Basics
import Prelude.Bool

-- Numerical Operator Precedence
infixl 5 ==, /=
infixl 6 <, <=, >, >=
infixl 7 <<, >>
infixl 8 +,-
infixl 9 *,/

-- ------------------------------------------------------------- [ Boolean Ops ]
intToBool : Int -> Bool
intToBool 0 = False
intToBool x = True

boolOp : (a -> a -> Int) -> a -> a -> Bool
boolOp op x y = intToBool (op x y)

-- ---------------------------------------------------------- [ Equality Interface ]
||| The Eq interface defines inequality and equality.
interface Eq a where
    (==) : a -> a -> Bool
    (/=) : a -> a -> Bool

    x /= y = not (x == y)
    x == y = not (x /= y)

implementation Eq () where
  () == () = True

implementation Eq Int where
    (==) = boolOp prim__eqInt

implementation Eq Integer where
    (==) = boolOp prim__eqBigInt

implementation Eq Double where
    (==) = boolOp prim__eqFloat

implementation Eq Char where
    (==) = boolOp prim__eqChar

implementation Eq String where
    (==) = boolOp prim__eqString

implementation Eq Ptr where
    (==) = boolOp prim__eqPtr

implementation Eq ManagedPtr where
    (==) = boolOp prim__eqManagedPtr

implementation Eq Bool where
    True  == True  = True
    True  == False = False
    False == True  = False
    False == False = True
    
implementation (Eq a, Eq b) => Eq (a, b) where
  (==) (a, c) (b, d) = (a == b) && (c == d)


-- ---------------------------------------------------------- [ Ordering Interface ]
%elim data Ordering = LT | EQ | GT

implementation Eq Ordering where
    LT == LT = True
    EQ == EQ = True
    GT == GT = True
    _  == _  = False

||| Compose two comparisons into the lexicographic product
thenCompare : Ordering -> Lazy Ordering -> Ordering
thenCompare LT y = LT
thenCompare EQ y = y
thenCompare GT y = GT

||| The Ord interface defines comparison operations on ordered data types.
interface Eq a => Ord a where
    compare : a -> a -> Ordering

    (<) : a -> a -> Bool
    (<) x y with (compare x y)
        (<) x y | LT = True
        (<) x y | _  = False

    (>) : a -> a -> Bool
    (>) x y with (compare x y)
        (>) x y | GT = True
        (>) x y | _  = False

    (<=) : a -> a -> Bool
    (<=) x y = x < y || x == y

    (>=) : a -> a -> Bool
    (>=) x y = x > y || x == y

    max : a -> a -> a
    max x y = if x > y then x else y

    min : a -> a -> a
    min x y = if (x < y) then x else y

implementation Ord () where
    compare () () = EQ

implementation Ord Int where
    compare x y = if (x == y) then EQ else
                  if (boolOp prim__sltInt x y) then LT else
                  GT


implementation Ord Integer where
    compare x y = if (x == y) then EQ else
                  if (boolOp prim__sltBigInt x y) then LT else
                  GT


implementation Ord Double where
    compare x y = if (x == y) then EQ else
                  if (boolOp prim__sltFloat x y) then LT else
                  GT


implementation Ord Char where
    compare x y = if (x == y) then EQ else
                  if (boolOp prim__sltChar x y) then LT else
                  GT


implementation Ord String where
    compare x y = if (x == y) then EQ else
                  if (boolOp prim__ltString x y) then LT else
                  GT


implementation Ord Bool where
    compare True True = EQ
    compare False False = EQ
    compare False True = LT
    compare True False = GT


implementation (Ord a, Ord b) => Ord (a, b) where
  compare (xl, xr) (yl, yr) =
    if xl /= yl
      then compare xl yl
      else compare xr yr

-- --------------------------------------------------------- [ Numerical Interface ]
||| The Num interface defines basic numerical arithmetic.
interface Num a where
    (+) : a -> a -> a
    (*) : a -> a -> a
    ||| Conversion from Integer.
    fromInteger : Integer -> a

implementation Num Integer where
    (+) = prim__addBigInt
    (*) = prim__mulBigInt

    fromInteger = id

implementation Num Int where
    (+) = prim__addInt
    (*) = prim__mulInt

    fromInteger = prim__truncBigInt_Int


implementation Num Double where
    (+) = prim__addFloat
    (*) = prim__mulFloat

    fromInteger = prim__toFloatBigInt

implementation Num Bits8 where
  (+) = prim__addB8
  (*) = prim__mulB8
  fromInteger = prim__truncBigInt_B8

implementation Num Bits16 where
  (+) = prim__addB16
  (*) = prim__mulB16
  fromInteger = prim__truncBigInt_B16

implementation Num Bits32 where
  (+) = prim__addB32
  (*) = prim__mulB32
  fromInteger = prim__truncBigInt_B32

implementation Num Bits64 where
  (+) = prim__addB64
  (*) = prim__mulB64
  fromInteger = prim__truncBigInt_B64

-- --------------------------------------------------------- [ Negatable Interface ]
||| The `Neg` interface defines operations on numbers which can be negative.
interface Num a => Neg a where
    ||| The underlying implementation of unary minus. `-5` desugars to `negate (fromInteger 5)`.
    negate : a -> a
    (-) : a -> a -> a
    ||| Absolute value
    abs : a -> a

implementation Neg Integer where
    negate x = prim__subBigInt 0 x
    (-) = prim__subBigInt
    abs x = if x < 0 then -x else x

implementation Neg Int where
    negate x = prim__subInt 0 x
    (-) = prim__subInt
    abs x = if x < (prim__truncBigInt_Int 0) then -x else x

implementation Neg Double where
    negate x = prim__negFloat x
    (-) = prim__subFloat
    abs x = if x < (prim__toFloatBigInt 0) then -x else x

-- ------------------------------------------------------------
implementation Eq Bits8 where
  x == y = intToBool (prim__eqB8 x y)

implementation Eq Bits16 where
  x == y = intToBool (prim__eqB16 x y)

implementation Eq Bits32 where
  x == y = intToBool (prim__eqB32 x y)

implementation Eq Bits64 where
  x == y = intToBool (prim__eqB64 x y)

implementation Ord Bits8 where
  (<) = boolOp prim__ltB8
  (>) = boolOp prim__gtB8
  (<=) = boolOp prim__lteB8
  (>=) = boolOp prim__gteB8
  compare l r = if l < r then LT
                else if l > r then GT
                     else EQ

implementation Ord Bits16 where
  (<) = boolOp prim__ltB16
  (>) = boolOp prim__gtB16
  (<=) = boolOp prim__lteB16
  (>=) = boolOp prim__gteB16
  compare l r = if l < r then LT
                else if l > r then GT
                     else EQ

implementation Ord Bits32 where
  (<) = boolOp prim__ltB32
  (>) = boolOp prim__gtB32
  (<=) = boolOp prim__lteB32
  (>=) = boolOp prim__gteB32
  compare l r = if l < r then LT
                else if l > r then GT
                     else EQ

implementation Ord Bits64 where
  (<) = boolOp prim__ltB64
  (>) = boolOp prim__gtB64
  (<=) = boolOp prim__lteB64
  (>=) = boolOp prim__gteB64
  compare l r = if l < r then LT
                else if l > r then GT
                     else EQ

-- ------------------------------------------------------------- [ Bounded ]

interface Ord b => MinBound b where
  ||| The lower bound for the type
  minBound : b

interface Ord b => MaxBound b where
  ||| The upper bound for the type
  maxBound : b

implementation MinBound Bits8 where
  minBound = 0x0

implementation MaxBound Bits8 where
  maxBound = 0xff

implementation MinBound Bits16 where
  minBound = 0x0

implementation MaxBound Bits16 where
  maxBound = 0xffff

implementation MinBound Bits32 where
  minBound = 0x0

implementation MaxBound Bits32 where
  maxBound = 0xffffffff

implementation MinBound Bits64 where
  minBound = 0x0

implementation MaxBound Bits64 where
  maxBound = 0xffffffffffffffff


-- ------------------------------------------------------------- [ Fractionals ]

||| Fractional division of two Doubles.
(/) : Double -> Double -> Double
(/) = prim__divFloat


-- --------------------------------------------------------------- [ Integrals ]
%default partial

interface Integral a where
   div : a -> a -> a
   mod : a -> a -> a

-- ---------------------------------------------------------------- [ Integers ]
divBigInt : Integer -> Integer -> Integer
divBigInt x y = case y == 0 of
  False => prim__sdivBigInt x y

modBigInt : Integer -> Integer -> Integer
modBigInt x y = case y == 0 of
  False => prim__sremBigInt x y

implementation Integral Integer where
  div = divBigInt
  mod = modBigInt

-- --------------------------------------------------------------------- [ Int ]

divInt : Int -> Int -> Int
divInt x y = case y == 0 of
  False => prim__sdivInt x y

modInt : Int -> Int -> Int
modInt x y = case y == 0 of
  False => prim__sremInt x y

implementation Integral Int where
  div = divInt
  mod = modInt

-- ------------------------------------------------------------------- [ Bits8 ]
divB8 : Bits8 -> Bits8 -> Bits8
divB8 x y = case y == 0 of
  False => prim__sdivB8 x y

modB8 : Bits8 -> Bits8 -> Bits8
modB8 x y = case y == 0 of
  False => prim__sremB8 x y
  
implementation Integral Bits8 where
  div = divB8
  mod = modB8

-- ------------------------------------------------------------------ [ Bits16 ]
divB16 : Bits16 -> Bits16 -> Bits16
divB16 x y = case y == 0 of
  False => prim__sdivB16 x y

modB16 : Bits16 -> Bits16 -> Bits16
modB16 x y = case y == 0 of
  False => prim__sremB16 x y

implementation Integral Bits16 where
  div = divB16 
  mod = modB16 

-- ------------------------------------------------------------------ [ Bits32 ]
divB32 : Bits32 -> Bits32 -> Bits32
divB32 x y = case y == 0 of
  False => prim__sdivB32 x y

modB32 : Bits32 -> Bits32 -> Bits32
modB32 x y = case y == 0 of
  False => prim__sremB32 x y

implementation Integral Bits32 where
  div = divB32 
  mod = modB32 

-- ------------------------------------------------------------------ [ Bits64 ]
divB64 : Bits64 -> Bits64 -> Bits64
divB64 x y = case y == 0 of
  False => prim__sdivB64 x y

modB64 : Bits64 -> Bits64 -> Bits64
modB64 x y = case y == 0 of
  False => prim__sremB64 x y

implementation Integral Bits64 where
  div = divB64 
  mod = modB64 


