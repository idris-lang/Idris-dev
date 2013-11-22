module Prelude.Basics

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

