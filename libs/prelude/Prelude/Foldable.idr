module Prelude.Foldable

import Builtins
import Prelude.Bool
import Prelude.Classes
import Prelude.Algebra

%access public
%default total

class Foldable (t : Type -> Type) where
  foldr : (elt -> acc -> acc) -> acc -> t elt -> acc

foldl : Foldable t => (acc -> elt -> acc) -> acc -> t elt -> acc
foldl f z t = foldr (flip (.) . flip f) id t z

concat : (Foldable t, Monoid a) => t a -> a
concat = foldr (<+>) neutral

concatMap : (Foldable t, Monoid m) => (a -> m) -> t a -> m
concatMap f = foldr ((<+>) . f) neutral

and : Foldable t => t (Lazy Bool) -> Bool
and = foldl (&&) True

or : Foldable t => t (Lazy Bool) -> Bool
or = foldl (||) False

any : Foldable t => (a -> Bool) -> t a -> Bool
any p = foldl (\x => \y => x || p y) False

all : Foldable t => (a -> Bool) -> t a -> Bool
all p = foldl (\x => \y => x && p y)  True

sum : (Foldable t, Num a) => t a -> a
sum = foldr (+) 0

product : (Foldable t, Num a) => t a -> a
product = foldr (*) 1

