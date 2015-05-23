module Predicates

%default total
%access public

||| A predicate on a type. It can be useful to think of a predicate
||| on a type as describing a set, where the type provides the
||| universe.
Pred : Type -> Type
Pred a = a -> Type

%name
Pred p,q

||| A relation between two (possibly equal) types
REL : Type -> Type -> Type
REL a b = a -> b -> Type

||| A relation on a single type
Rel : Type -> Type
Rel a = a -> a -> Type  -- = REL a

Subset : Rel (Pred a)
Subset {a} p1 p2 = {x : a} -> p1 x -> p2 x

||| A family of predicates on a type
Family : Type -> Type -> Type
Family a ix = (i : ix) -> Pred a

Intersection : Family a ix -> Pred a
Intersection {ix} f x = (i : ix) -> f i x

Intersection2 : Pred a -> Pred a -> Pred a
Intersection2 p q x = (p x, q x)

Union : Family a ix -> Pred a
Union {ix} f x = (i ** f i x)

Union2 : Pred a -> Pred a -> Pred a
Union2 p q x = Either (p x) (q x)

Invert : Pred a -> Pred a
Invert p x = Not (p x)

||| Proof that a function from `a` to `b` is a function from `p` to `q`;
||| This definition comes from Agda.
IsFunction : Pred a -> Pred b -> Pred (a -> b)
IsFunction p q f = p `Subset` (q . f)

||| A type for functions themselves. A function of type `Function p q`
||| represents a function from `p` to `q`. We *cannot* generally use this
||| sort of function to produce a function between the underlying types!
Function : (p : Pred a) -> (q : Pred b) -> Type
Function {a} {b} p q = (x : a) -> p x -> (y ** q y)

||| Given a function that passes `IsFunction`, we can produce a
||| corresponding `Function`.
IsFunToFun : (f : a -> b) -> IsFunction p q f -> Function p q
IsFunToFun f isFunf x px = (f x ** isFunf px)
