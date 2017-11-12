||| Monads and Functors
module Prelude.Monad

import Builtins
import Prelude.Functor
import public Prelude.Applicative
import Prelude.Basics
import Prelude.Foldable
import IO

%access public export

infixl 1 >>=

interface Applicative m => Monad (m : Type -> Type) where
    ||| Also called `bind`.
    (>>=)  : m a -> ((result : a) -> m b) -> m b

    ||| Also called `flatten` or mu
    join : m (m a) -> m a

    -- default implementations
    (>>=) x f = join (f <$> x)
    join x = x >>= id

||| For compatibility with Haskell. Note that monads are **not** free to
||| define `return` and `pure` differently!
return : Monad m => a -> m a
return = pure
%fragile return "`return` is provided for those coming from Haskell. Please use `pure` instead, which is equivalent."

||| Similar to `foldl`, but uses a function wrapping its result in a `Monad`.
||| Consequently, the final value is wrapped in the same `Monad`.
foldlM : (Foldable t, Monad m) => (funcM: a -> b -> m a) -> (init: a) -> (input: t b) -> m a
foldlM fm a0 = foldl (\ma,b => ma >>= flip fm b) (pure a0)

-- Annoyingly, these need to be here, so that we can use them in other
-- Prelude modules other than the top level.

Functor (IO' ffi) where
    map f io = io_bind io (\b => io_pure (f b))

Applicative (IO' ffi) where
    pure x = io_pure x
    f <*> a = io_bind f (\f' =>
                io_bind a (\a' =>
                  io_pure (f' a')))


Monad (IO' ffi) where
    b >>= k = io_bind b k
