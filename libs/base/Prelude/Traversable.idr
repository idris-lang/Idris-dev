module Prelude.Traversable

import Prelude.Applicative
import Prelude.Foldable

traverse_ : (Foldable t, Applicative f) => (a -> f b) -> t a -> f ()
traverse_ f = foldr (($>) . f) (pure ())

sequence_ : (Foldable t, Applicative f) => t (f a) -> f ()
sequence_ = foldr ($>) (pure ())

class (Functor t, Foldable t) => Traversable (t : Type -> Type) where
  traverse : Applicative f => (a -> f b) -> t a -> f (t b)

sequence : (Traversable t, Applicative f) => t (f a) -> f (t a)
sequence = traverse id
