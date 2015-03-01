module Prelude.Functor

import Prelude.Basics

infixl 4 <$>

||| Functors
||| @ f the action of the functor on objects
class Functor (f : Type -> Type) where
    ||| The action of the functor on morphisms
    ||| @ f the functor
    ||| @ m the morphism
    (<$>) : (m : a -> b) -> f a -> f b

class Functor f => VerifiedFunctor (f : Type -> Type) where
  functorIdentity : {a : Type} -> (x : f a) -> id <$> x = id x
  functorComposition : {a : Type} -> {b : Type} -> (x : f a) ->
                       (g1 : a -> b) -> (g2 : b -> c) ->
                       (g2 . g1) <$> x = ((<$>) g2 . (<$>) g1) x

instance Functor id where
    f <$> a = f a

map : Functor f => (a -> b) -> f a -> f b
map = (<$>)
