module Prelude.Monad

-- Monads and Functors

import Builtins
import Prelude.List
import Prelude.Applicative

%access public

infixl 5 >>=

class Applicative m => Monad (m : Type -> Type) where 
    return : a -> m a
    (>>=)  : m a -> (a -> m b) -> m b

flatten : Monad m => m (m a) -> m a
flatten a = a >>= id
