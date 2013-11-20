module Control.Monad.State

import Control.Monad.Identity
import Prelude.Monad
import Prelude.Functor

%access public

class Monad m => MonadState s (m : Type -> Type) where
    get : m s
    put : s -> m ()

record StateT : Type -> (Type -> Type) -> Type -> Type where
    ST : {m : Type -> Type} ->
         (runStateT : s -> m (a, s)) -> StateT s m a

instance Functor f => Functor (StateT s f) where
    map f (ST g) = ST (\st => map (mapFst f) (g st)) where
       mapFst : (a -> x) -> (a, b) -> (x, b)
       mapFst fn (a, b) = (fn a, b)

instance Monad f => Applicative (StateT s f) where
    pure x = ST (\st => pure (x, st))

    (ST f) <$> (ST a) = ST (\st => do (g, r) <- f st
                                      (b, t) <- a r
                                      return (g b, t))

instance Monad m => Monad (StateT s m) where
    (ST f) >>= k = ST (\st => do (v, st') <- f st
                                 let ST kv = k v
                                 kv st')

instance Monad m => MonadState s (StateT s m) where
    get   = ST (\x => return (x, x))
    put x = ST (\y => return ((), x))

modify : MonadState s m => (s -> s) -> m ()
modify f = do s <- get
              put (f s)

gets : MonadState s m => (s -> a) -> m a
gets f = do s <- get
            return (f s)

State : Type -> Type -> Type
State s a = StateT s Identity a
