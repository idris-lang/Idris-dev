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

class Monad m => MonadPlus (m : Type -> Type) where 
    mplus : m a -> m a -> m a
    mzero : m a

mapM : Monad m => (a -> m b) -> List a -> m (List b)
mapM f xs = sequence (map f xs)

mapM_ : Monad m => (a -> m b) -> List a -> m ()
mapM_ f xs = sequence_ (map f xs)

flatten : Monad m => m (m a) -> m a
flatten a = a >>= id
