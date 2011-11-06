data Sigma : (a : Set) -> (P : a -> Set) -> Set where
    Exists : {P : a -> Set} -> (x : a) -> P x -> Sigma a P;

getSigIdx : {P : a -> Set} -> Sigma a P -> a;
getSigIdx (Exists a v) = a;

getSigVal : {P : a -> Set} -> (s : Sigma a P) -> P (getSigIdx s);
getSigVal (Exists a v) = v;

-- For rewrite tactic
replace : {a:_} -> {x:_} -> {y:_} -> {P : a -> Set} -> x = y -> P x -> P y;
replace refl prf = prf;

sym : {x:a} -> {y:a} -> x = y -> y = x;
sym refl = refl;

lazy : a -> a;
lazy x = x; -- compiled specially

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

data Num : Set -> Set where
    NumInstance : (plus : a -> a -> a) -> 
                  (sub  : a -> a -> a) ->
                  (mult : a -> a -> a) ->
                  Num a;

    (+) : Num a => a -> a -> a;
    (+) @{ NumInstance p s m } x y = p x y;

    (-) : Num a => a -> a -> a;
    (-) @{ NumInstance p s m } x y = s x y;

    (*) : Num a => a -> a -> a;
    (*) @{ NumInstance p s m } x y = m x y;

instance numInt : Num Int;
instance numInt = NumInstance prim__addInt prim__subInt prim__mulInt;

instance numFloat : Num Float;
instance numFloat = NumInstance prim__addFloat prim__subFloat prim__mulFloat;

data Eq : Set -> Set where
    EqInstance : (eq : a -> a -> Bool) ->
                 (neq : a -> a -> Bool) ->
                 Eq a;

    (==) : Eq a => a -> a -> Bool;
    (==) @{ EqInstance eq neq } x y = eq x y;

    (/=) : Eq a => a -> a -> Bool;
    (/=) @{ EqInstance eq neq } x y = neq x y;

instance EqInt : Eq Int;
instance EqInt = EqInstance (boolOp prim__eqInt) (\x, y => not (x == y));

instance EqFloat : Eq Float;
instance EqFloat = EqInstance (boolOp prim__eqFloat) (\x, y => not (x == y));  

data Ordering = LT | EQ | GT;

data Ord : Set -> Set where
    OrdInstance : Eq a => 
                  (compare : a -> a -> Ordering) ->
                  Ord a;

    compare : Ord a => a -> a -> Ordering;
    compare @{ OrdInstance c } = c;

instance OrdInt : Ord Int;
instance OrdInt = OrdInstance cmpInt where {
    cmpInt : Int -> Int -> Ordering;
    cmpInt x y = if (x == y) then EQ else
                 if (boolOp prim__ltInt x y) then LT else
                 GT;
}

instance OrdFloat : Ord Float;
instance OrdFloat = OrdInstance cmpFloat where {
    cmpFloat : Float -> Float -> Ordering;
    cmpFloat x y = if (x == y) then EQ else
                   if (boolOp prim__ltFloat x y) then LT else
                   GT;
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


