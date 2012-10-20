module control.category

import prelude.morphisms

class Category (cat : Set -> Set -> Set) where
  id  : cat a a
  (.) : cat b c -> cat a b -> cat a c

instance Category Morphism where
  id = Homo builtins.id
  (Homo f) . (Homo g) = Homo $ builtins.(.) f g

infixr 1 >>>
(>>>) : Category cat => cat a b -> cat b c -> cat a c
f >>> g = g . f
