module Data.BoundedList

%access public
%default total

data BoundedList : Type -> Nat -> Type where
  Nil : BoundedList a n
  (::) : a -> BoundedList a n -> BoundedList a (S n)

length : BoundedList a n -> Fin (S n)
length [] = fO
length (x :: xs) = fS (length xs)

--------------------------------------------------------------------------------
-- Indexing into bounded lists
--------------------------------------------------------------------------------

index : Fin (S n) -> BoundedList a n -> Maybe a
index _      []        = Nothing
index fO     (x :: _)  = Just x
index (fS f) (_ :: xs) = index f xs

--------------------------------------------------------------------------------
-- Adjusting bounds
--------------------------------------------------------------------------------

weaken : BoundedList a n -> BoundedList a (n + m)
weaken []        = []
weaken (x :: xs) = x :: weaken xs

--------------------------------------------------------------------------------
-- Conversions to and from list
--------------------------------------------------------------------------------

take : (n : Nat) -> List a -> BoundedList a n
take _ [] = []
take Z _ = []
take (S n') (x :: xs) = x :: take n' xs

toList : BoundedList a n -> List a
toList [] = []
toList (x :: xs) = x :: toList xs

fromList : (xs : List a) -> BoundedList a (length xs)
fromList [] = []
fromList (x :: xs) = x :: fromList xs

--------------------------------------------------------------------------------
-- Building (bigger) bounded lists
--------------------------------------------------------------------------------

replicate : (n : Nat) -> a -> BoundedList a n
replicate Z _ = []
replicate (S n) x = x :: replicate n x

--------------------------------------------------------------------------------
-- Folds
--------------------------------------------------------------------------------

foldl : (a -> b -> a) -> a -> BoundedList b n -> a
foldl f e []      = e
foldl f e (x::xs) = foldl f (f e x) xs

foldr : (a -> b -> b) -> b -> BoundedList a n -> b
foldr f e []      = e
foldr f e (x::xs) = f x (foldr f e xs)

--------------------------------------------------------------------------------
-- Maps
--------------------------------------------------------------------------------

map : (a -> b) -> BoundedList a n -> BoundedList b n
map f [] = []
map f (x :: xs) = f x :: map f xs

--------------------------------------------------------------------------------
-- Misc
--------------------------------------------------------------------------------

%assert_total -- not sure why this isn't accepted - clearly decreasing on n
pad : (xs : BoundedList a n) -> (padding : a) -> BoundedList a n
pad {n=Z}    []        _       = []
pad {n=S n'} []        padding = padding :: (pad {n=n'} [] padding)
pad {n=S n'} (x :: xs) padding = x :: pad {n=n'} xs padding


--------------------------------------------------------------------------------
-- Simple properties
--------------------------------------------------------------------------------

zeroBoundIsEmpty : (xs : BoundedList a 0) -> xs = the (BoundedList a 0) []
zeroBoundIsEmpty [] = refl
zeroBoundIsEmpty (_ :: _) impossible