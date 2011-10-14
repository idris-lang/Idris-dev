import nat;

data Bool = False | True;

infixl 5 ==, /=, ==.;
infixl 6 <, <=, >, >=, <., <=., >., >=.;
infixl 7 <<, >>;
infixl 8 +,-,++,+.,-.;
infixl 9 *,/,*.,/.;

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

