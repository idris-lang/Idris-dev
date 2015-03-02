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

class (Monad m, VerifiedApplicative m) => VerifiedMonad (m : Type -> Type) where
  monadApplicative : (mf : m (a -> b)) -> (mx : m a) ->
                     mf <*> mx = mf >>= \f =>
                                 mx >>= \x =>
                                        pure (f x)
  monadLeftIdentity : (x : a) -> (f : a -> m b) -> return x >>= f = f x
  monadRightIdentity : (mx : m a) -> mx >>= return = mx
  monadAssociativity : (mx : m a) -> (f : a -> m b) -> (g : b -> m c) ->
                       (mx >>= f) >>= g = mx >>= (\x => f x >>= g)

instance Monad id where
    a >>= f = f a

||| Also called `join` or mu
flatten : Monad m => m (m a) -> m a
flatten a = a >>= id

||| For compatibility with Haskell. Note that monads are **not** free to
||| define `return` and `pure` differently!
return : Monad m => a -> m a
return = pure
