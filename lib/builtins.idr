data Sigma : (a : Set) -> (P : a -> Set) -> Set where
    Exists : {P : a -> Set} -> (x : a) -> P x -> Sigma a P;

getSigIdx : {P : a -> Set} -> Sigma a P -> a;
getSigIdx (Exists a v) = a;

getSigVal : {P : a -> Set} -> (s : Sigma a P) -> P (getSigIdx s);
getSigVal (Exists a v) = v;

-- For rewrite tactic
replace : {a:_} -> {x:_} -> {y:_} -> {P : a -> Set} -> x = y -> P x -> P y;
replace refl prf = prf;

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

(+) : Int -> Int -> Int;
(+) = prim__addInt;

(-) : Int -> Int -> Int;
(-) = prim__subInt;

(*) : Int -> Int -> Int;
(*) = prim__mulInt;

div : Int -> Int -> Int;
div = prim__divInt;

(==) : Int -> Int -> Bool;
(==) = boolOp prim__eqInt;

(<) : Int -> Int -> Bool;
(<) = boolOp prim__ltInt;

(<=) : Int -> Int -> Bool;
(<=) = boolOp prim__lteInt;

(>) : Int -> Int -> Bool;
(>) = boolOp prim__gtInt;

(>=) : Int -> Int -> Bool;
(>=) = boolOp prim__gteInt;

(+.) : Float -> Float -> Float;
(+.) = prim__addFloat;

(-.) : Float -> Float -> Float;
(-.) = prim__subFloat;

(*.) : Float -> Float -> Float;
(*.) = prim__mulFloat;

(/.) : Float -> Float -> Float;
(/.) = prim__divFloat;

(==.) : Float -> Float -> Bool;
(==.) = boolOp prim__eqFloat;

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


