module Prelude.Traversable

import Builtins

import Prelude.Basics
import Prelude.Applicative
import Prelude.Foldable
import Prelude.Functor

%access public export

||| Map each element of a structure to a computation, evaluate those
||| computations and discard the results.
traverse_ : (Foldable t, Applicative f) => (a -> f b) -> t a -> f ()
traverse_ f = foldr ((*>) . f) (pure ())

||| Evaluate each computation in a structure and discard the results
sequence_ : (Foldable t, Applicative f) => t (f a) -> f ()
sequence_ = foldr (*>) (pure ())

||| Like `traverse_` but with the arguments flipped
for_ : (Foldable t, Applicative f) => t a -> (a -> f b) -> f ()
for_ = flip traverse_

interface (Functor t, Foldable t) => Traversable (t : Type -> Type) where
  ||| Map each element of a structure to a computation, evaluate those
  ||| computations and combine the results.
  traverse : Applicative f => (a -> f b) -> t a -> f (t b)

||| Evaluate each computation in a structure and collect the results
sequence : (Traversable t, Applicative f) => t (f a) -> f (t a)
sequence = traverse id

||| Like `traverse` but with the arguments flipped
for : (Traversable t, Applicative f) => t a -> (a -> f b) -> f (t b)
for = flip traverse
