module Prelude.Functor

class Functor (f : Type -> Type) where
    map : (a -> b) -> f a -> f b
