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

-- ---------------------------------------------------------- [ Equality Class ]
||| The Eq class defines inequality and equality.
class Eq a where
    (==) : a -> a -> Bool
    (/=) : a -> a -> Bool

    x /= y = not (x == y)
    x == y = not (x /= y)

instance Eq () where
  () == () = True

instance Eq Int where
    (==) = boolOp prim__eqInt

instance Eq Integer where
    (==) = boolOp prim__eqBigInt

instance Eq Float where
    (==) = boolOp prim__eqFloat

instance Eq Char where
    (==) = boolOp prim__eqChar

instance Eq String where
    (==) = boolOp prim__eqString

instance Eq Bool where
    True  == True  = True
    True  == False = False
    False == True  = False
    False == False = True
    
instance (Eq a, Eq b) => Eq (a, b) where
  (==) (a, c) (b, d) = (a == b) && (c == d)


-- ---------------------------------------------------------- [ Ordering Class ]
%elim data Ordering = LT | EQ | GT

instance Eq Ordering where
    LT == LT = True
    EQ == EQ = True
    GT == GT = True
    _  == _  = False

||| The Ord class defines comparison operations on ordered data types.
class Eq a => Ord a where
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
    max x y = if (x > y) then x else y

    min : a -> a -> a
    min x y = if (x < y) then x else y

instance Ord () where
    compare () () = EQ

instance Ord Int where
    compare x y = if (x == y) then EQ else
                  if (boolOp prim__sltInt x y) then LT else
                  GT


instance Ord Integer where
    compare x y = if (x == y) then EQ else
                  if (boolOp prim__sltBigInt x y) then LT else
                  GT


instance Ord Float where
    compare x y = if (x == y) then EQ else
                  if (boolOp prim__sltFloat x y) then LT else
                  GT


instance Ord Char where
    compare x y = if (x == y) then EQ else
                  if (boolOp prim__sltChar x y) then LT else
                  GT


instance Ord String where
    compare x y = if (x == y) then EQ else
                  if (boolOp prim__ltString x y) then LT else
                  GT


instance Ord Bool where
    compare True True = EQ
    compare False False = EQ
    compare False True = LT
    compare True False = GT


instance (Ord a, Ord b) => Ord (a, b) where
  compare (xl, xr) (yl, yr) =
    if xl /= yl
      then compare xl yl
      else compare xr yr

-- --------------------------------------------------------- [ Negatable Class ]
||| The `Neg` class defines unary negation (-).
class Neg a where
    ||| The underlying implementation of unary minus. `-5` desugars to `negate (fromInteger 5)`.
    negate : a -> a

instance Neg Integer where
    negate x = prim__subBigInt 0 x

instance Neg Int where
    negate x = prim__subInt 0 x

instance Neg Float where
    negate x = prim__negFloat x

-- --------------------------------------------------------- [ Numerical Class ]
||| The Num class defines basic numerical arithmetic.
class Num a where
    (+) : a -> a -> a
    (-) : a -> a -> a
    (*) : a -> a -> a
    ||| Absolute value
    abs : a -> a
    ||| Conversion from Integer.
    fromInteger : Integer -> a

instance Num Integer where
    (+) = prim__addBigInt
    (-) = prim__subBigInt
    (*) = prim__mulBigInt

    abs x = if x < 0 then -x else x
    fromInteger = id

instance Num Int where
    (+) = prim__addInt
    (-) = prim__subInt
    (*) = prim__mulInt

    fromInteger = prim__truncBigInt_Int
    abs x = if x < (prim__truncBigInt_Int 0) then -x else x


instance Num Float where
    (+) = prim__addFloat
    (-) = prim__subFloat
    (*) = prim__mulFloat

    abs x = if x < (prim__toFloatBigInt 0) then -x else x
    fromInteger = prim__toFloatBigInt

instance Num Bits8 where
  (+) = prim__addB8
  (-) = prim__subB8
  (*) = prim__mulB8
  abs = id
  fromInteger = prim__truncBigInt_B8

instance Num Bits16 where
  (+) = prim__addB16
  (-) = prim__subB16
  (*) = prim__mulB16
  abs = id
  fromInteger = prim__truncBigInt_B16

instance Num Bits32 where
  (+) = prim__addB32
  (-) = prim__subB32
  (*) = prim__mulB32
  abs = id
  fromInteger = prim__truncBigInt_B32

instance Num Bits64 where
  (+) = prim__addB64
  (-) = prim__subB64
  (*) = prim__mulB64
  abs = id
  fromInteger = prim__truncBigInt_B64

instance Eq Bits8 where
  x == y = intToBool (prim__eqB8 x y)

instance Eq Bits16 where
  x == y = intToBool (prim__eqB16 x y)

instance Eq Bits32 where
  x == y = intToBool (prim__eqB32 x y)

instance Eq Bits64 where
  x == y = intToBool (prim__eqB64 x y)

instance Ord Bits8 where
  (<) = boolOp prim__ltB8
  (>) = boolOp prim__gtB8
  (<=) = boolOp prim__lteB8
  (>=) = boolOp prim__gteB8
  compare l r = if l < r then LT
                else if l > r then GT
                     else EQ

instance Ord Bits16 where
  (<) = boolOp prim__ltB16
  (>) = boolOp prim__gtB16
  (<=) = boolOp prim__lteB16
  (>=) = boolOp prim__gteB16
  compare l r = if l < r then LT
                else if l > r then GT
                     else EQ

instance Ord Bits32 where
  (<) = boolOp prim__ltB32
  (>) = boolOp prim__gtB32
  (<=) = boolOp prim__lteB32
  (>=) = boolOp prim__gteB32
  compare l r = if l < r then LT
                else if l > r then GT
                     else EQ

instance Ord Bits64 where
  (<) = boolOp prim__ltB64
  (>) = boolOp prim__gtB64
  (<=) = boolOp prim__lteB64
  (>=) = boolOp prim__gteB64
  compare l r = if l < r then LT
                else if l > r then GT
                     else EQ

-- ------------------------------------------------------------- [ Bounded ]

class Ord b => MinBound b where
  ||| The lower bound for the type
  minBound : b

class Ord b => MaxBound b where
  ||| The upper bound for the type
  maxBound : b

instance MinBound Bits8 where
  minBound = 0x0

instance MaxBound Bits8 where
  maxBound = 0xff

instance MinBound Bits16 where
  minBound = 0x0

instance MaxBound Bits16 where
  maxBound = 0xffff

instance MinBound Bits32 where
  minBound = 0x0

instance MaxBound Bits32 where
  maxBound = 0xffffffff

instance MinBound Bits64 where
  minBound = 0x0

instance MaxBound Bits64 where
  maxBound = 0xffffffffffffffff


-- ------------------------------------------------------------- [ Fractionals ]

||| Fractional division of two Floats.
(/) : Float -> Float -> Float
(/) = prim__divFloat


-- --------------------------------------------------------------- [ Integrals ]
%default partial

class Integral a where
   zero : a
   divNZ : a -> (y: a) -> Not (y = zero) -> a
   modNZ : a -> (y: a) -> Not (y = zero) -> a

-- ---------------------------------------------------------------- [ Integers ]
divBigInt : Integer -> (y: Integer) -> Not (y = (the Integer 0)) -> Integer
divBigInt x y _ = prim__sdivBigInt x y

modBigInt : Integer -> (y: Integer) -> Not (y = (the Integer 0)) -> Integer
modBigInt x y _ = prim__sremBigInt x y

instance Integral Integer where
  zero  = 0
  divNZ = divBigInt
  modNZ = modBigInt

-- --------------------------------------------------------------------- [ Int ]

divInt : Int -> (y: Int) -> Not (y = (the Int 0)) -> Int
divInt x y _ = prim__sdivInt x y

modInt : Int -> (y: Int) -> Not (y = (the Int 0)) -> Int
modInt x y _ = prim__sremInt x y

instance Integral Int where
  zero  = 0
  divNZ = divInt
  modNZ = modInt

-- ------------------------------------------------------------------- [ Bits8 ]
divB8 : Bits8 -> (y: Bits8) -> Not (y = (the Bits8 0)) -> Bits8
divB8 x y _ = prim__sdivB8 x y

modB8 : Bits8 -> (y: Bits8) -> Not (y = (the Bits8 0)) -> Bits8
modB8 x y _ = prim__sremB8 x y
  
instance Integral Bits8 where
  zero  = 0
  divNZ = divB8
  modNZ = modB8

-- ------------------------------------------------------------------ [ Bits16 ]
divB16 : Bits16 -> (y: Bits16) -> Not (y = (the Bits16 0)) -> Bits16
divB16 x y _ = prim__sdivB16 x y

modB16 : Bits16 -> (y: Bits16) -> Not (y = (the Bits16 0)) -> Bits16
modB16 x y _ = prim__sremB16 x y

instance Integral Bits16 where
  zero  = 0
  divNZ = divB16 
  modNZ = modB16 

-- ------------------------------------------------------------------ [ Bits32 ]
divB32 : Bits32 -> (y: Bits32) -> Not (y = (the Bits32 0)) -> Bits32
divB32 x y _ = prim__sdivB32 x y

modB32 : Bits32 -> (y: Bits32) -> Not (y = (the Bits32 0)) -> Bits32
modB32 x y _ = prim__sremB32 x y

instance Integral Bits32 where
  zero  = 0
  divNZ = divB32 
  modNZ = modB32 

-- ------------------------------------------------------------------ [ Bits64 ]
divB64 : Bits64 -> (y: Bits64) -> Not (y = (the Bits64 0)) -> Bits64
divB64 x y _ = prim__sdivB64 x y

modB64 : Bits64 -> (y: Bits64) -> Not (y = (the Bits64 0)) -> Bits64
modB64 x y _ = prim__sremB64 x y

instance Integral Bits64 where
  zero  = 0
  divNZ = divB64 
  modNZ = modB64 

