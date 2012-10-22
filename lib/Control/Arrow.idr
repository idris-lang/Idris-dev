module Category.Arrow

import Prelude.Morphisms
import Control.Category

infixr 3 ***
infixr 3 &&&

class Category arr => Arrow (arr : Set -> Set -> Set) where
  arrow  : (a -> b) -> arr a b
  first  : arr a b -> arr (a, c) (b, c)
  second : arr a b -> arr (c, a) (c, b)
  (***)  : arr a b -> arr a' b' -> arr (a, a') (b, b')
  (&&&)  : arr a b -> arr a b' -> arr a (b, b')

instance Arrow Morphism where
  arrow  f              = Homo f
  first  (Homo f)       = Homo $ \(a, b) => (f a, b)
  second (Homo f)       = Homo $ \(a, b) => (a, f b)
  (Homo f) *** (Homo g) = Homo $ \(a, b) => (f a, g b)
  (Homo f) &&& (Homo g) = Homo $ \a => (f a, g a)
