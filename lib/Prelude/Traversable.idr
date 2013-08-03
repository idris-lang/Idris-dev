module Prelude.Traversable

import Prelude.Applicative
import Prelude.Foldable

traverse_ : (Foldable t, Applicative f) => (a -> f b) -> t a -> f ()
traverse_ f = foldr (($>) . f) (pure ())

sequence_ : (Foldable t, Applicative f) => t (f a) -> f ()
sequence_ = foldr ($>) (pure ())

