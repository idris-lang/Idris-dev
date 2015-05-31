module Prelude.Foldable

import Builtins
import Prelude.Bool
import Prelude.Basics
import Prelude.Classes
import Prelude.Algebra

%access public
%default total

|||Anything `Foldable` can be reduced to a summary value using a provided operation.
class Foldable (t : Type -> Type) where
  ||| Fold the structure from the right.
  |||
  ||| @f The folding function.
  ||| @res The initial value to fold into.
  ||| @t The structure we are folding
  foldr : (f : item -> res -> res) -> res -> t item -> res

  ||| Fold the structure from the left.
  |||
  ||| This has a default implementation using `foldr`.
  |||
  ||| @f The folding function.
  ||| @res The initial value to fold into.
  ||| @t The structure we are folding
  foldl : (f : res -> item -> res) -> res -> t item -> res
  foldl f z t = foldr (flip (.) . flip f) id t z

||| Combine each element of a structure into a monoid
concat : (Foldable t, Monoid a) => t a -> a
concat = foldr (<+>) neutral

||| Combine into a monoid the collective results of applying a function
||| to each element of a structure
concatMap : (Foldable t, Monoid m) => (a -> m) -> t a -> m
concatMap f = foldr ((<+>) . f) neutral

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
