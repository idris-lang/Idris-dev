module Control.Category

import Data.Morphisms

%access public export

interface Category (cat : Type -> Type -> Type) where
  id  : cat a a
  (.) : cat b c -> cat a b -> cat a c

implementation Category Morphism where
  id                = Mor id
  -- disambiguation needed below, because unification can now get further
  -- here with Category.(.) and it's only interface resolution that fails!
  (Mor f) . (Mor g) = with Basics (Mor (f . g))

implementation Monad m => Category (Kleislimorphism m) where
  id                        = Kleisli (pure . id)
  (Kleisli f) . (Kleisli g) = Kleisli $ \a => g a >>= f

infixr 1 >>>
(>>>) : Category cat => cat a b -> cat b c -> cat a c
f >>> g = g . f
