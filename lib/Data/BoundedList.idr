module Data.BoundedList

%default total

data BoundedList : Type -> Nat -> Type where
  Nil : BoundedList a n
  (::) : a -> BoundedList a n -> BoundedList a (S n)

length : BoundedList a n -> Fin (S n)
length [] = fO
length (x :: xs) = fS (length xs)

index : Fin (S n) -> BoundedList a n -> Maybe a
index _      []        = Nothing
index fO     (x :: _)  = Just x
index (fS f) (_ :: xs) = index f xs

weaken : BoundedList a n -> BoundedList a (n + m)
weaken []        = []
weaken (x :: xs) = x :: weaken xs

take : (n : Nat) -> List a -> BoundedList a n
take _ [] = []
take O _ = []
take (S n') (x :: xs) = x :: take n' xs

toList : BoundedList a n -> List a
toList [] = []
toList (x :: xs) = x :: toList xs

fromList : (xs : List a) -> BoundedList a (length xs)
fromList [] = []
fromList (x :: xs) = x :: fromList xs

map : (a -> b) -> BoundedList a n -> BoundedList b n
map f [] = []
map f (x :: xs) = f x :: map f xs

zeroBoundIsEmpty : (xs : BoundedList a 0) -> xs = the (BoundedList a 0) []
zeroBoundIsEmpty [] = refl
zeroBoundIsEmpty (_ :: _) impossible

