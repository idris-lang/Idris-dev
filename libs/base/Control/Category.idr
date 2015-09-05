module Control.Category

import Data.Morphisms

%access public

class Category (cat : Type -> Type -> Type) where
  id  : cat a a
  (.) : cat b c -> cat a b -> cat a c

instance Category Morphism where
  id                = Mor id
  -- disambiguation needed below, because unification can now get further
  -- here with Category.(.) and it's only type class resolution that fails!
  (Mor f) . (Mor g) = with Basics (Mor (f . g))

instance Monad m => Category (Kleislimorphism m) where
  id                        = Kleisli (return . id)
  (Kleisli f) . (Kleisli g) = Kleisli $ \a => g a >>= f

infixr 1 >>>
(>>>) : Category cat => cat a b -> cat b c -> cat a c
f >>> g = g . f
