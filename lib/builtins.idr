%access public

data Exists : (a : Set) -> (P : a -> Set) -> Set where
    Ex_intro : {P : a -> Set} -> (x : a) -> P x -> Exists a P

getWitness : {P : a -> Set} -> Exists a P -> a
getWitness (a ** v) = a

getProof : {P : a -> Set} -> (s : Exists a P) -> P (getWitness s)
getProof (a ** v) = v

FalseElim : _|_ -> a

-- For rewrite tactic
replace : {a:_} -> {x:_} -> {y:_} -> {P : a -> Set} -> x = y -> P x -> P y
replace refl prf = prf

sym : {l:a} -> {r:a} -> l = r -> r = l
sym refl = refl

lazy : a -> a
lazy x = x -- compiled specially

malloc : Int -> a -> a
malloc size x = x -- compiled specially

trace_malloc : a -> a
trace_malloc x = x -- compiled specially

believe_me : a -> b -- compiled specially as id, use with care!
believe_me x = prim__believe_me _ _ x

namespace builtins {

id : a -> a
id x = x

const : a -> b -> a
const x _ = x

fst : (s, t) -> s
fst (x, y) = x

snd : (a, b) -> b
snd (x, y) = y

infixl 9 .

(.) : (b -> c) -> (a -> b) -> a -> c
(.) f g x = f (g x)

flip : (a -> b -> c) -> b -> a -> c
flip f x y = f y x

infixr 1 $

($) : (a -> b) -> a -> b
f $ a = f a

cong : {f : t -> u} -> (a = b) -> f a = f b
cong refl = refl

data Bool = False | True

boolElim : (x:Bool) -> |(t : a) -> |(f : a) -> a 
boolElim True  t e = t
boolElim False t e = e

data so : Bool -> Set where oh : so True

syntax if [test] then [t] else [e] = boolElim test t e
syntax [test] "?" [t] ":" [e] = if test then t else e

infixl 4 &&, ||

(||) : Bool -> Bool -> Bool
(||) False x = x
(||) True _  = True

(&&) : Bool -> Bool -> Bool
(&&) True x  = x
(&&) False _ = False

not : Bool -> Bool
not True = False
not False = True

infixl 5 ==, /=, ==.
infixl 6 <, <=, >, >=, <., <=., >., >=.
infixl 7 <<, >>
infixl 8 +,-,++,+.,-.
infixl 9 *,/,*.,/.

--- Numeric operators

intToBool : Int -> Bool
intToBool 0 = False
intToBool x = True

boolOp : (a -> a -> Int) -> a -> a -> Bool
boolOp op x y = intToBool (op x y) 

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

instance (Eq a, Eq b) => Eq (a, b) where
  (==) (a, c) (b, d) = (a == b) && (c == d)


data Ordering = LT | EQ | GT

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
                  if (boolOp prim__ltInt x y) then LT else
                  GT


instance Ord Integer where 
    compare x y = if (x == y) then EQ else
                  if (boolOp prim__ltBigInt x y) then LT else
                  GT


instance Ord Float where 
    compare x y = if (x == y) then EQ else
                  if (boolOp prim__ltFloat x y) then LT else
                  GT


instance Ord Char where 
    compare x y = if (x == y) then EQ else
                  if (boolOp prim__ltChar x y) then LT else
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


class Num a where 
    (+) : a -> a -> a
    (-) : a -> a -> a
    (*) : a -> a -> a

    abs : a -> a
    fromInteger : Int -> a



instance Num Int where 
    (+) = prim__addInt
    (-) = prim__subInt
    (*) = prim__mulInt

    fromInteger = id
    abs x = if x<0 then -x else x


instance Num Integer where 
    (+) = prim__addBigInt
    (-) = prim__subBigInt
    (*) = prim__mulBigInt

    abs x = if x<0 then -x else x
    fromInteger = prim__intToBigInt


instance Num Float where 
    (+) = prim__addFloat
    (-) = prim__subFloat
    (*) = prim__mulFloat

    abs x = if x<0 then -x else x
    fromInteger = prim__intToFloat 


div : Int -> Int -> Int
div = prim__divInt


(/) : Float -> Float -> Float
(/) = prim__divFloat

--- string operators

(++) : String -> String -> String
(++) = prim__concat

strHead : String -> Char
strHead = prim__strHead

strTail : String -> String
strTail = prim__strTail

strCons : Char -> String -> String
strCons = prim__strCons

strIndex : String -> Int -> Char
strIndex = prim__strIndex

reverse : String -> String
reverse = prim__strRev

}

