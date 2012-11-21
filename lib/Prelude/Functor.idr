module Prelude.Functor

class Functor (f : Set -> Set) where 
    fmap : (a -> b) -> f a -> f b
