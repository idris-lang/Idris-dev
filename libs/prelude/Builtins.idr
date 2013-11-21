%access public
%default total

data Exists : (a : Type) -> (P : a -> Type) -> Type where
    Ex_intro : {P : a -> Type} -> (x : a) -> P x -> Exists a P

getWitness : {P : a -> Type} -> Exists a P -> a
getWitness (a ** v) = a

getProof : {P : a -> Type} -> (s : Exists a P) -> P (getWitness s)
getProof (a ** v) = v

FalseElim : _|_ -> a

-- ------------------------------------------------------ [ For rewrite tactic ]
replace : {a:_} -> {x:_} -> {y:_} -> {P : a -> Type} -> x = y -> P x -> P y
replace refl prf = prf

sym : {l:a} -> {r:a} -> l = r -> r = l
sym refl = refl

trans : {a:x} -> {b:x} -> {c:x} -> a = b -> b = c -> a = c
trans refl refl = refl

lazy : a -> a
lazy x = x -- compiled specially

par : |(thunk:a) -> a
par x = x -- compiled specially

malloc : Int -> a -> a
malloc size x = x -- compiled specially

trace_malloc : a -> a
trace_malloc x = x -- compiled specially

abstract %assert_total -- need to pretend
believe_me : a -> b -- compiled specially as id, use with care!
believe_me x = prim__believe_me _ _ x

public %assert_total -- reduces at compile time, use with extreme care!
really_believe_me : a -> b
really_believe_me x = prim__believe_me _ _ x

-- ---------------------------------------------------------------- [ Builtins ]
namespace Builtins {

Not : Type -> Type
Not a = a -> _|_

-- | Identity function.
id : a -> a
id x = x

-- | Manually assign a type to an expression.
the : (a : Type) -> a -> a
the _ = id

-- | Constant function.
const : a -> b -> a
const x _ = x

-- | Return the first element of a pair.
fst : (s, t) -> s
fst (x, y) = x

-- | Return the second element of a pair.
snd : (a, b) -> b
snd (x, y) = y

infixl 9 .

-- | Function composition
(.) : (b -> c) -> (a -> b) -> a -> c
(.) f g x = f (g x)

-- | Takes in the first two arguments in reverse order.
flip : (a -> b -> c) -> b -> a -> c
flip f x y = f y x

infixr 1 $

-- | Function application.
($) : (a -> b) -> a -> b
f $ a = f a

cong : {f : t -> u} -> (a = b) -> f a = f b
cong refl = refl

data Dec : Type -> Type where
    Yes : {A : Type} -> A          -> Dec A
    No  : {A : Type} -> (A -> _|_) -> Dec A

-- | Boolean Data Type
data Bool = False | True

-- | Boolean elimination
boolElim : Bool -> |(t : a) -> |(f : a) -> a
boolElim True  t e = t
boolElim False t e = e

-- | Defines a predicate on Bool which guarantees that the value is true.
data so : Bool -> Type where oh : so True

-- Syntaxtic sugar for boolean elimination.
syntax if [test] then [t] else [e] = boolElim test t e
syntax [test] "?" [t] ":" [e] = if test then t else e

-- Boolean Operator Precedence
infixl 4 &&, ||

-- | Boolean OR
(||) : Bool -> Bool -> Bool
(||) False x = x
(||) True _  = True

-- | Boolean AND
(&&) : Bool -> Bool -> Bool
(&&) True x  = x
(&&) False _ = False

-- | Boolean NOT
not : Bool -> Bool
not True = False
not False = True

-- Numerical Operator Precedence
infixl 5 ==, /=
infixl 6 <, <=, >, >=
infixl 7 <<, >>
infixl 8 +,-,++
infixl 9 *,/

-- ------------------------------------------------------- [ Numeric Operators ]
intToBool : Int -> Bool
intToBool 0 = False
intToBool x = True

boolOp : (a -> a -> Int) -> a -> a -> Bool
boolOp op x y = intToBool (op x y)

-- | The Eq class defines inequality and equality.
class Eq a where
    (==) : a -> a -> Bool
    (/=) : a -> a -> Bool

    x /= y = not (x == y)
    x == y = not (x /= y)

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


data Ordering = LT | EQ | GT

instance Eq Ordering where
    LT == LT = True
    EQ == EQ = True
    GT == GT = True
    _  == _  = False

-- | The Ord class defines comparison operations on ordered data types.
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


instance (Ord a, Ord b) => Ord (a, b) where
  compare (xl, xr) (yl, yr) =
    if xl /= yl
      then compare xl yl
      else compare xr yr

-- | The Num class defines basic numerical arithmetic.
class Num a where
    (+) : a -> a -> a
    (-) : a -> a -> a
    (*) : a -> a -> a
    -- | Absolute value
    abs : a -> a
    -- | Conversion from Integer.
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

-- | Integer division.
partial
div : Integer -> Integer -> Integer
div = prim__sdivBigInt

-- | Integer modulus.
partial
mod : Integer -> Integer -> Integer
mod = prim__sremBigInt

-- | Fractional division of two Floats.
(/) : Float -> Float -> Float
(/) = prim__divFloat

-- -------------------------------------------------------- [ String Operators ]
-- | Appends two strings together.
(++) : String -> String -> String
(++) = prim__concat

-- | Returns the first character in the specified string.
partial
strHead : String -> Char
strHead = prim__strHead

-- | Returns the characters specified after the head of the string.
partial
strTail : String -> String
strTail = prim__strTail

-- | Adds a character to the from of the specified string.
strCons : Char -> String -> String
strCons = prim__strCons

-- | Returns the nth character (starting from 0) of the specified string.
partial
strIndex : String -> Int -> Char
strIndex = prim__strIndex

-- | Reverses the elements within a String.
reverse : String -> String
reverse = prim__strRev

null : Ptr
null = prim__null

}

