module Control.Monad.State

import Control.Monad.Identity
import Prelude.Monad
import Prelude.Functor

%access public

class Monad m => MonadState s (m : Set -> Set) where
    get : m s
    put : s -> m ()

record StateT : Set -> (Set -> Set) -> Set -> Set where
    ST : {m : Set -> Set} ->
         (runStateT : s -> m (a, s)) -> StateT s m a

instance Functor f => Functor (StateT s f) where
    fmap f (ST g) = ST (\st => fmap (mapFst f) (g st)) where
       mapFst : (a -> x) -> (a, b) -> (x, b)
       mapFst fn (a, b) = (fn a, b)

instance Monad f => Applicative (StateT s f) where
    pure x = ST (\st => pure (x, st))

    (ST f) <$> (ST a) = ST (\st => do (g, r) <- f st
                                      (b, t) <- a r
                                      pure (g b, t))

instance Monad m => Monad (StateT s m) where
    (ST f) >>= k = ST (\st => do (v, st') <- f st
                                 let ST kv = k v
                                 kv st')

instance Monad m => MonadState s (StateT s m) where
    get   = ST (\x => pure (x, x))
    put x = ST (\y => pure ((), x)) 

State : Set -> Set -> Set
State s a = StateT s Identity a

