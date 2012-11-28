module Prelude.Functor

-- Functor: instances should satisfy the following laws:
--   Functor fmap:
--                     fmap id        == id
--     forall f g .    fmap (f . g)   == fmap f . fmap g

class Functor (f : Set -> Set) where 
    fmap : (a -> b) -> (f a -> f b)
