module Prelude.Monad

-- Monads and Functors

import Builtins
import Prelude.Functor
import Prelude.Applicative
import Prelude.Basics
import IO

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

-- Annoyingly, these need to be here, so that we can use them in other
-- Prelude modules other than the top level.

instance Functor (IO' ffi) where
    map f io = io_bind io (\b => io_return (f b))

instance Applicative (IO' ffi) where
    pure x = io_return x
    f <*> a = io_bind f (\f' =>
                io_bind a (\a' =>
                  io_return (f' a')))


instance Monad (IO' ffi) where
    b >>= k = io_bind b k

