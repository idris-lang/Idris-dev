module Prelude.Functor

import Prelude.Basics

%access public export

||| Functors allow a uniform action over a parameterised type.
||| @ f a parameterised type 
interface Functor (f : Type -> Type) where
    ||| Apply a function across everything of type 'a' in a 
    ||| parameterised type
    ||| @ f the parameterised type
    ||| @ func the function to apply
    map : (func : a -> b) -> f a -> f b

infixl 4 <$>

||| An infix alias for `map`, applying a function across everything of
||| type 'a' in a parameterised type
||| @ f the parameterised type
||| @ func the function to apply
(<$>) : Functor f => (func : a -> b) -> f a -> f b
func <$> x = map func x

