module Prelude.Foldable

import Builtins
import Prelude.Bool
import Prelude.Classes
import Prelude.Algebra
import Data.Morphisms

%access public
%default total

||| Data structures that can be reduced to a single value in a meaningful way
class Foldable (t : Type -> Type) where
  ||| Combine all elements of a structure with a monoid
  fold : Monoid m => t m -> m
  fold = foldMap id

  ||| Map each element of a structure to a monoid then combine them
  foldMap : Monoid m => (a -> m) -> t m -> m
  foldMap f = foldr ((<+>) . f) neutral

  ||| Right-associative fold
  foldr : (elt -> acc -> acc) -> acc -> t elt -> acc
  foldr f z t = applyEndo (foldMap (Endo . f) t) z

  ||| Left-associative fold
  foldl : Foldable t => (acc -> elt -> acc) -> acc -> t elt -> acc
  foldl f z t = foldr (flip (.) . flip f) id t z

||| Combine each element of a structure into a monoid
concat : (Foldable t, Monoid a) => t a -> a
concat = foldr (<+>) neutral

||| Combine into a monoid the collective results of applying a function
||| to each element of a structure
concatMap : (Foldable t, Monoid m) => (a -> m) -> t a -> m
concatMap f = foldr ((<+>) . f) neutral

||| Right-associative monadic fold over a structure
foldrM : (Foldable t, Monad m) => (a -> b -> m b) -> b -> t a -> m b
foldrM f z0 xs = foldl f' return xs z0
  where f' k x z = f x z >>= k

||| Left-associative monadic fold over a structure
foldlM : (Foldable t, Monad m) => (b -> a -> m b) -> b -> t a -> m b
foldlM f z0 xs = foldr f' return xs z0
  where f' x k z = f z x >>= k

||| The conjunction of all elements of a structure containing
||| lazy boolean values. `and` short-circuits from left to right,
||| evaluating until either an element is `False` or no elements remain.
and : Foldable t => t (Lazy Bool) -> Bool
and = foldl (&&) True

||| The disjunction of all elements of a structure containing
||| lazy boolean values. `or` short-circuits from left to right, evaluating
||| either until an element is `True` or no elements remain.
or : Foldable t => t (Lazy Bool) -> Bool
or = foldl (||) False

||| The disjunction of the collective results of applying a
||| predicate to all elements of a structure. `any` short-circuits
||| from left to right.
any : Foldable t => (a -> Bool) -> t a -> Bool
any p = foldl (\x,y => x || p y) False

||| The disjunction of the collective results of applying a
||| predicate to all elements of a structure. `all` short-circuits
||| from left to right.
all : Foldable t => (a -> Bool) -> t a -> Bool
all p = foldl (\x,y => x && p y)  True

||| Add together all the elements of a structure
sum : (Foldable t, Num a) => t a -> a
sum = foldr (+) 0

||| Multiply together all elements of a structure
product : (Foldable t, Num a) => t a -> a
product = foldr (*) 1
