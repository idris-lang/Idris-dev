module Prelude.Functor

||| Functors
||| @ f the action of the functor on objects
class Functor (f : Type -> Type) where
    ||| The action of the functor on morphisms
    ||| @ f the functor
    ||| @ m the morphism
    map : (m : a -> b) -> f a -> f b
