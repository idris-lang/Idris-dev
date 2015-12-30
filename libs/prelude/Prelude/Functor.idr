module Prelude.Functor

import Prelude.Basics

||| Functors allow a uniform action over a parameterised type.
||| @ f a parameterised type 
class Functor (f : Type -> Type) where
    ||| Apply a function across everything of type 'a' in a 
    ||| parameterised type
    ||| @ f the parameterised type
    ||| @ m the function to apply
    map : (m : a -> b) -> f a -> f b

infixl 4 <$>

||| An infix alias for `map`, applying a function across everything of
||| type 'a' in a parameterised type
||| @ f the parameterised type
||| @ m the function to apply
(<$>) : Functor f => (m : a -> b) -> f a -> f b
m <$> x = map m x

