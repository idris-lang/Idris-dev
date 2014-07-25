module Control.Category

import Data.Morphisms

%access public

class Semigroupoid (s : Type -> Type -> Type) where
  (.) : s b c -> s a b -> s a c

class Semigroupoid cat => Category (cat : Type -> Type -> Type) where
  id  : cat a a

instance Semigroupoid Morphism where
  (Mor f) . (Mor g) = Mor (f . g)
instance Category Morphism where
  id                = Mor id

instance Monad m => Semigroupoid (Kleislimorphism m) where
  (Kleisli f) . (Kleisli g) = Kleisli $ \a => g a >>= f
instance Monad m => Category (Kleislimorphism m) where
  id                        = Kleisli (pure . id)

infixr 1 >>>
(>>>) : Semigroupoid cat => cat a b -> cat b c -> cat a c
f >>> g = g . f
