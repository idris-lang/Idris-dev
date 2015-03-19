module Control.Monad.State

import Control.Monad.Identity
import Control.Monad.Trans

%access public

||| A computation which runs in a context and produces an output
class Monad m => MonadState s (m : Type -> Type) where
    ||| Get the context
    get : m s
    ||| Write a new context/output
    put : s -> m ()

||| The transformer on which the State monad is based
record StateT (s : Type) (m : Type -> Type) (a : Type) where
  constructor ST
  runStateT : s -> m (a, s)

instance Functor f => Functor (StateT s f) where
    map f (ST g) = ST (\st => map (mapFst f) (g st)) where
       mapFst : (a -> x) -> (a, s) -> (x, s)
       mapFst fn (a, b) = (fn a, b)

instance Monad f => Applicative (StateT s f) where
    pure x = ST (\st => pure (x, st))

    (ST f) <*> (ST a) = ST (\st => do (g, r) <- f st
                                      (b, t) <- a r
                                      return (g b, t))

instance Monad m => Monad (StateT s m) where
    (ST f) >>= k = ST (\st => do (v, st') <- f st
                                 let ST kv = k v
                                 kv st')

instance Monad m => MonadState s (StateT s m) where
    get   = ST (\x => return (x, x))
    put x = ST (\y => return ((), x))

instance MonadTrans (StateT s) where
    lift x = ST (\st => do r <- x
                           return (r, st))

||| Apply a function to modify the context of this computation
modify : MonadState s m => (s -> s) -> m ()
modify f = do s <- get
              put (f s)

||| Evaluate a function in the context held by this computation
gets : MonadState s m => (s -> a) -> m a
gets f = do s <- get
            return (f s)

||| The State monad. See the MonadState class
State : Type -> Type -> Type
State s a = StateT s Identity a
