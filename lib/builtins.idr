data Sigma : (a : Set) -> (P : a -> Set) -> Set where
    Exists : {P : a -> Set} -> (x : a) -> P x -> Sigma a P;

getSigIdx : {P : a -> Set} -> Sigma a P -> a;
getSigIdx (Exists a v) = a;

getSigVal : {P : a -> Set} -> (s : Sigma a P) -> P (getSigIdx s);
getSigVal (Exists a v) = v;

id : a -> a;
id x = x;

fst : (s, t) -> s;
fst (x, y) = x;

snd : (a, b) -> b;
snd (x, y) = y;

infixl 9 .;

(.) : (b -> c) -> (a -> b) -> a -> c;
(.) f g x = f (g x);


