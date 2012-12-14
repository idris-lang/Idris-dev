module Prelude.Applicative

import Builtins
import Prelude.Functor

---- Applicative functors/Idioms

infixl 2 <$> 

class Functor f => Applicative (f : Type -> Type) where 
    pure  : a -> f a
    (<$>) : f (a -> b) -> f a -> f b 

class Applicative f => Alternative (f : Type -> Type) where
    empty : f a
    (<|>) : f a -> f a -> f a

guard : Alternative f => Bool -> f ()
guard a = if a then pure () else empty
