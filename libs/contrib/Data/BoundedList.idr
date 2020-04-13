module Data.BoundedList

import Data.Fin
import Data.Vect

%access public export
%default total

||| A list with an upper bound on its length.
data BoundedList : Nat -> Type -> Type where
  Nil : BoundedList n a
  (::) : a -> BoundedList n a -> BoundedList (S n) a

||| Compute the length of a list.
length : BoundedList n a -> Fin (S n)
length [] = FZ
length (x :: xs) = FS (length xs)

--------------------------------------------------------------------------------
-- Indexing into bounded lists
--------------------------------------------------------------------------------

index : Fin (S n) -> BoundedList n a -> Maybe a
index _      []        = Nothing
index FZ     (x :: _)  = Just x
index (FS f) (_ :: xs) = index f xs

--------------------------------------------------------------------------------
-- Adjusting bounds
--------------------------------------------------------------------------------

||| Loosen the bounds on a list's length.
weaken : BoundedList n a -> BoundedList (n + m) a
weaken []        = []
weaken (x :: xs) = x :: weaken xs

--------------------------------------------------------------------------------
-- Conversions to and from list
--------------------------------------------------------------------------------

take : (n : Nat) -> List a -> BoundedList n a
take _ [] = []
take Z _ = []
take (S n') (x :: xs) = x :: take n' xs

toList : BoundedList n a -> List a
toList [] = []
toList (x :: xs) = x :: Data.BoundedList.toList xs

fromList : (xs : List a) -> BoundedList (length xs) a
fromList [] = []
fromList (x :: xs) = x :: fromList xs

--------------------------------------------------------------------------------
-- Conversions to and from vector
--------------------------------------------------------------------------------

||| Convert bounded list to vector.
toVect : (xs : BoundedList n a) -> Vect (finToNat (length xs)) a
toVect [] = []
toVect (x :: xs) = x :: toVect xs

||| Convert vector to bounded list.
fromVect : (xs : Vect n a) -> BoundedList n a
fromVect [] = []
fromVect (x :: xs) = x :: fromVect xs

--------------------------------------------------------------------------------
-- Building (bigger) bounded lists
--------------------------------------------------------------------------------

replicate : (n : Nat) -> a -> BoundedList n a
replicate Z _ = []
replicate (S n) x = x :: replicate n x

--------------------------------------------------------------------------------
-- Folds
--------------------------------------------------------------------------------

implementation Foldable (BoundedList n) where
  foldr f e []      = e
  foldr f e (x::xs) = f x (foldr f e xs)
  foldl f e []      = e
  foldl f e (x::xs) = foldl f (f e x) xs

--------------------------------------------------------------------------------
-- Maps
--------------------------------------------------------------------------------

implementation Functor (BoundedList n) where
  map f [] = []
  map f (x :: xs) = f x :: map f xs

--------------------------------------------------------------------------------
-- Monoid
--------------------------------------------------------------------------------

implementation Semigroup a => Semigroup (BoundedList n a) where
  (x :: xs) <+> (y :: ys) = (x <+> y) :: (xs <+> ys)
  xs <+> [] = xs
  [] <+> ys = ys

  semigroupOpIsAssociative [] [] [] = Refl
  semigroupOpIsAssociative [] [] (_ :: _) = Refl
  semigroupOpIsAssociative [] (_ :: _) [] = Refl
  semigroupOpIsAssociative [] (_ :: _) (_ :: _) = Refl
  semigroupOpIsAssociative (_ :: _) [] [] = Refl
  semigroupOpIsAssociative (_ :: _) [] (_ :: _) = Refl
  semigroupOpIsAssociative (_ :: _) (_ :: _) [] = Refl
  semigroupOpIsAssociative (x :: xs) (y :: ys) (z :: zs) =
    rewrite semigroupOpIsAssociative x y z in
      rewrite semigroupOpIsAssociative xs ys zs in
        Refl

-- The Semigroup constraint is only needed because that's how we make a
-- semigroup from BoundedList, not used in this implementation.
implementation Semigroup a => Monoid (BoundedList n a) where
  neutral = []

  monoidNeutralIsNeutralL [] = Refl
  monoidNeutralIsNeutralL (_ :: _) = Refl
  monoidNeutralIsNeutralR [] = Refl
  monoidNeutralIsNeutralR (_ :: _) = Refl

--------------------------------------------------------------------------------
-- Misc
--------------------------------------------------------------------------------

||| Extend a bounded list to the maximum size by padding on the left.
pad : BoundedList n a -> a -> BoundedList n a
pad {n=Z}    []        _       = []
pad {n=S n'} []        padding = padding :: (pad {n=n'} [] padding)
pad {n=S n'} (x :: xs) padding = x :: pad {n=n'} xs padding


--------------------------------------------------------------------------------
-- Simple properties
--------------------------------------------------------------------------------

zeroBoundIsEmpty : (xs : BoundedList 0 a) -> xs = the (BoundedList 0 a) []
zeroBoundIsEmpty [] = Refl
zeroBoundIsEmpty (_ :: _) impossible
