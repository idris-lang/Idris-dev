module Prelude.Functor

class Functor (f : Type -> Type) where 
    fmap : (a -> b) -> f a -> f b
