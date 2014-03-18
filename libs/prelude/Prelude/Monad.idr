module Prelude.Monad

-- Monads and Functors

import Builtins
import Prelude.List
import Prelude.Applicative

%access public

infixl 5 >>=

class Applicative m => Monad (m : Type -> Type) where
    (>>=)  : m a -> (a -> m b) -> m b

||| Also called `join` or mu
flatten : Monad m => m (m a) -> m a
flatten a = a >>= id

||| For compatibility with Haskell. Note that monads are **not** free to
||| define `return` and `pure` differently!
return : Monad m => a -> m a
return = pure
