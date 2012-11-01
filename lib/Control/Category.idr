module Control.Category

import Data.Morphisms

%access public

class Category (cat : Set -> Set -> Set) where
  id  : cat a a
  (.) : cat b c -> cat a b -> cat a c

instance Category Homomorphism where
  id                  = Homo Builtins.id
  (Homo f) . (Homo g) = Homo $ Builtins.(.) f g

infixr 1 >>>
(>>>) : Category cat => cat a b -> cat b c -> cat a c
f >>> g = g . f
