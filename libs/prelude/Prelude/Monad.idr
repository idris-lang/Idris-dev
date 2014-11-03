module Prelude.Monad

-- Monads and Functors

import Builtins
import Prelude.List
import Prelude.Applicative
import Prelude.Basics

%access public

infixl 5 >>=

class Applicative m => Monad (m : Type -> Type) where
    (>>=)  : m a -> (a -> m b) -> m b

class Monad m => VerifiedMonad (m : Type -> Type) where
  total lIdentity : (f : a -> m b) -> (x : a) -> return x >>= f = f x
  total rIdentity : (ma : m a) -> ma >>= return = ma
  total associativity : (ma : m a) -> (f : a -> m b) -> (g : b -> m c) ->
                        (ma >>= f) >>= g = ma >>= (\x => f x >>= g)

instance Monad id where
    a >>= f = f a

||| Also called `join` or mu
flatten : Monad m => m (m a) -> m a
flatten a = a >>= id

||| For compatibility with Haskell. Note that monads are **not** free to
||| define `return` and `pure` differently!
return : Monad m => a -> m a
return = pure
