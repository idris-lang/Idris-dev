module Prelude.Traversable

import Builtins

import Prelude.Basics
import Prelude.Applicative
import Prelude.Foldable
import Prelude.Functor

traverse_ : (Foldable t, Applicative f) => (a -> f b) -> t a -> f ()
traverse_ f = foldr ((*>) . f) (pure ())

sequence_ : (Foldable t, Applicative f) => t (f a) -> f ()
sequence_ = foldr (*>) (pure ())

for_ : (Foldable t, Applicative f) => t a -> (a -> f b) -> f ()
for_ = flip traverse_

interface (Functor t, Foldable t) => Traversable (t : Type -> Type) where
  traverse : Applicative f => (a -> f b) -> t a -> f (t b)

sequence : (Traversable t, Applicative f) => t (f a) -> f (t a)
sequence = traverse id

for : (Traversable t, Applicative f) => t a -> (a -> f b) -> f (t b)
for = flip traverse
