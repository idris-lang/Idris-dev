module Prelude.Traversable

import Prelude.Applicative
import Prelude.Foldable

traverse_ : (Foldable t, Applicative f) => (a -> f b) -> t a -> f ()
traverse_ f = foldr (($>) . f) (pure ())

sequence_ : (Foldable t, Applicative f) => t (f a) -> f ()
sequence_ = foldr ($>) (pure ())

for_ : (Foldable t, Applicative f) => t a -> (a -> f b) -> f ()
for_ = flip traverse_

class (Functor t, Foldable t) => Traversable (t : Type -> Type) where
  traverse : Applicative f => (a -> f b) -> t a -> f (t b)
class (Foldable1 t, Traversable t) => Traversable1 (t : Type -> Type) where
  traverse1 : Apply f => (a -> f b) -> t a -> f (t b)

sequence : (Traversable t, Applicative f) => t (f a) -> f (t a)
sequence = traverse id

sequence1 : (Traversable1 t, Apply f) => t (f a) -> f (t a)
sequence1 = traverse1 id

for : (Traversable t, Applicative f) => t a -> (a -> f b) -> f (t b)
for = flip traverse
