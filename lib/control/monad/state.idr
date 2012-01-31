module control.monad.state

import control.monad.identity
import prelude.monad

%access public

class Monad m => MonadState s (m : Set -> Set) where
    get : m s
    put : s -> m ()

record StateT : Set -> (Set -> Set) -> Set -> Set where
    ST : {m : Set -> Set} ->
         (runStateT : s -> m (a, s)) -> StateT s m a

instance Monad m => Monad (StateT s m) where
    return x = ST (\st => return (x, st))

    (ST f) >>= k = ST (\st => do (v, st') <- f st
                                 let ST kv = k v
                                 kv st')

instance Monad m => MonadState s (StateT s m) where
    get   = ST (\x => return (x, x))
    put x = ST (\y => return ((), x)) 

State : Set -> Set -> Set
State s a = StateT s Identity a

