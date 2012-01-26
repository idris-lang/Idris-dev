module algebra

import builtins

-- Sets with an associative binary operation
-- Must satisfy:
--   forall a, b, c. a <*> (b <*> c) = (a <*> b) <*> c
class Semigroup a where
  (<*>)        : a -> a -> a

-- Sets with an associative binary operation and a neutral element
-- Must satisfy:
--   forall a, b, c. a <*> (b <*> c) = (a <*> b) <*> c
--   forall a.       neutral <*> a   = a <*> neutral   = a
class Semigroup a => Monoid a where
  neutral : a

-- Sets with an associative binary operation, a neutral element, as well as
-- inverses
-- Must satisfy:
--   forall a, b, c. a <*> (b <*> c)     = (a <*> b) <*> c
--   forall a.       neutral <*> a       = a <*> neutral   = a
--   forall a.       inverse a <*> a     = a <*> inverse   = neutral
--   forall a.       inverse (inverse a) = a
class Monoid a => Group a where
  inverse : a -> a
  (<->)   : a -> a -> a

-- XXX: to add:
--   ring, field, euclidean domain, abelian group, vector spaces, etc.?
--   do we want proofs of properties in the type classes?
--   derived classes, some mechanism for multiple e.g. monoids on same type
