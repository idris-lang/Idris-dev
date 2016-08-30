module Prelude.Foldable

import Builtins
import Prelude.Bool
import Prelude.Basics
import Prelude.Interfaces
import Prelude.Algebra

%access public export
%default total

||| The `Foldable` interface describes how you can iterate over the
||| elements in a parameterised type and combine the elements
||| together, using a provided function, into a single result.
|||
||| @t The type of the 'Foldable' parameterised type.
interface Foldable (t : Type -> Type) where

  ||| Successively combine the elements in a parameterised type using
  ||| the provided function, starting with the element that is in the
  ||| final position i.e. the right-most position.
  |||
  ||| @func  The function used to 'fold' an element into the accumulated result.
  ||| @input The parameterised type.
  ||| @init  The starting value the results are being combined into.
  foldr : (func : elem -> acc -> acc) -> (init : acc) -> (input : t elem) -> acc

  ||| The same as `foldr` but begins the folding from the element at
  ||| the initial position in the data structure i.e. the left-most
  ||| position.
  |||
  ||| @func  The function used to 'fold' an element into the accumulated result.
  ||| @input The parameterised type.
  ||| @init  The starting value the results are being combined into.
  foldl : (func : acc -> elem -> acc) -> (init : acc) -> (input : t elem) -> acc
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
