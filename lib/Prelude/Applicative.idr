module Prelude.Applicative

import Builtins
import Prelude.Functor

---- Applicative functors/Idioms

infixl 2 <$> 

class Functor f => Applicative (f : Set -> Set) where 
    pure  : a -> f a
    (<$>) : f (a -> b) -> f a -> f b 


