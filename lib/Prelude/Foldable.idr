module Prelude.Foldable

import Builtins
import Prelude.Algebra

%access public
%default total

class Foldable (t : Type -> Type) where
  foldr : (elt -> acc -> acc) -> acc -> t elt -> acc

foldl : Foldable t => (acc -> elt -> acc) -> acc -> t elt -> acc
foldl f z t = foldr (flip (.) . flip f) id t z

concat : (Foldable t, Monoid a) => t a -> a
concat = foldr (<+>) neutral

and : Foldable t => t Bool -> Bool
and = foldr (&&) True

or : Foldable t => t Bool -> Bool
or = foldr (||) False

any : (Foldable t, Functor t) => (a -> Bool) -> t a -> Bool
any p = Foldable.or . fmap p

all : (Foldable t, Functor t) => (a -> Bool) -> t a -> Bool
all p = Foldable.and . fmap p

