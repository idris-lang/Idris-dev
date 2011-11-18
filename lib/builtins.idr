data Sigma : (a : Set) -> (P : a -> Set) -> Set where
    Exists : {P : a -> Set} -> (x : a) -> P x -> Sigma a P;

getWitness : {P : a -> Set} -> Sigma a P -> a;
getWitness (Exists a v) = a;

getProof : {P : a -> Set} -> (s : Sigma a P) -> P (getWitness s);
getProof (Exists a v) = v;

FalseElim : _|_ -> a;

-- For rewrite tactic
replace : {a:_} -> {x:_} -> {y:_} -> {P : a -> Set} -> x = y -> P x -> P y;
replace refl prf = prf;

sym : {x:a} -> {y:a} -> x = y -> y = x;
sym refl = refl;

lazy : a -> a;
lazy x = x; -- compiled specially

believe_me : a -> b; -- compiled specially as id, use with care!

id : a -> a;
id x = x;

fst : (s, t) -> s;
fst (x, y) = x;

snd : (a, b) -> b;
snd (x, y) = y;

infixl 9 .;

(.) : (b -> c) -> (a -> b) -> a -> c;
(.) f g x = f (g x);

infixr 1 $;

($) : (a -> b) -> a -> b;
f $ a = f a;

data Bool = False | True;

boolElim : (x:Bool) -> |(t : a) -> |(f : a) -> a; 
boolElim True  t e = t;
boolElim False t e = e;

data so : Bool -> Set where oh : so True;

syntax if [test] then [t] else [e] = boolElim test t e;

infix 4 &&, ||;

(||) : Bool -> Bool -> Bool;
(||) False x = x;
(||) True _  = True;

(&&) : Bool -> Bool -> Bool;
(&&) True x  = x;
(&&) False _ = False;

not : Bool -> Bool;
not True = False;
not False = True;

infixl 5 ==, /=, ==.;
infixl 6 <, <=, >, >=, <., <=., >., >=.;
infixl 7 <<, >>;
infixl 8 +,-,++,+.,-.;
infixl 9 *,/,*.,/.;

--- Numeric operators

intToBool : Int -> Bool;
intToBool 0 = False;
intToBool x = True;

boolOp : (a -> a -> Int) -> a -> a -> Bool;
boolOp op x y = intToBool (op x y); 

class Eq a where {
    (==) : a -> a -> Bool;
    (/=) : a -> a -> Bool;
}

instance Eq Int where {
    (==) = boolOp prim__eqInt;
    (/=) x y = not (x == y);
}

instance Eq Integer where {
    (==) = boolOp prim__eqBigInt;
    (/=) x y = not (x == y);
}

instance Eq Float where {
    (==) = boolOp prim__eqFloat;
    (/=) x y = not (x == y);
}

data Ordering = LT | EQ | GT;

class Eq a => Ord a where {
    compare : a -> a -> Ordering;
}

instance Ord Int where {
    compare x y = if (x == y) then EQ else
                  if (boolOp prim__ltInt x y) then LT else
                  GT;
}

instance Ord Float where {
    compare x y = if (x == y) then EQ else
                  if (boolOp prim__ltFloat x y) then LT else
                  GT;
}

class Eq a => Num a where {
    (+) : a -> a -> a;
    (-) : a -> a -> a;
    (*) : a -> a -> a;

    fromInteger : Int -> a;
}

instance Num Int where {
    (+) = prim__addInt;
    (-) = prim__subInt;
    (*) = prim__mulInt;

    fromInteger = id;
}

instance Num Integer where {
    (+) = prim__addBigInt;
    (-) = prim__subBigInt;
    (*) = prim__mulBigInt;

    fromInteger = prim__intToBigInt;
}

instance Num Float where {
    (+) = prim__addFloat;
    (-) = prim__subFloat;
    (*) = prim__mulFloat;

    fromInteger = prim__intToFloat; 
}

div : Int -> Int -> Int;
div = prim__divInt;

(<) : Int -> Int -> Bool;
(<) = boolOp prim__ltInt;

(<=) : Int -> Int -> Bool;
(<=) = boolOp prim__lteInt;

(>) : Int -> Int -> Bool;
(>) = boolOp prim__gtInt;

(>=) : Int -> Int -> Bool;
(>=) = boolOp prim__gteInt;

(/) : Float -> Float -> Float;
(/) = prim__divFloat;

(<.) : Float -> Float -> Bool;
(<.) = boolOp prim__ltFloat;

(<=.) : Float -> Float -> Bool;
(<=.) = boolOp prim__lteFloat;

(>.) : Float -> Float -> Bool;
(>.) = boolOp prim__gtFloat;

(>=.) : Float -> Float -> Bool;
(>=.) = boolOp prim__gteFloat;

--- string operators

(++) : String -> String -> String;
(++) = prim__concat;


