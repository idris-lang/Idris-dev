module Prelude.Monad

-- Monads and Functors

import Builtins
import Prelude.List
import Prelude.Applicative
import Prelude.Basics

%access public

infixl 5 >>=

class Apply m => Bind (m : Type -> Type) where
    (>>=)  : m a -> (a -> m b) -> m b

class (Applicative m, Bind m) => Monad (m : Type -> Type)

instance Bind id where
    a >>= f = f a

||| Also called `join` or mu
flatten : Bind m => m (m a) -> m a
flatten a = a >>= id

||| For compatibility with Haskell. Note that monads are **not** free to
||| define `return` and `pure` differently!
return : Monad m => a -> m a
return = pure
