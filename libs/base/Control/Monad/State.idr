module Control.Monad.State

import public Control.Monad.Identity
import public Control.Monad.Trans

%access public export

||| A computation which runs in a context and produces an output
interface Monad m => MonadState stateType (m : Type -> Type) | m where
    ||| Get the context
    get : m stateType
    ||| Write a new context/output
    put : stateType -> m ()

||| The transformer on which the State monad is based
record StateT (stateType : Type) (m : Type -> Type) (a : Type) where
  constructor ST
  runStateT : stateType -> m (a, stateType)

implementation Functor f => Functor (StateT stateType f) where
    map f (ST g) = ST (\st => map (mapFst f) (g st)) where
       mapFst : (a -> x) -> (a, s) -> (x, s)
       mapFst fn (a, b) = (fn a, b)

implementation Monad f => Applicative (StateT stateType f) where
    pure x = ST (\st => pure (x, st))

    (ST f) <*> (ST a) = ST (\st => do (g, r) <- f st
                                      (b, t) <- a r
                                      pure (g b, t))

implementation Monad m => Monad (StateT stateType m) where
    (ST f) >>= k = ST (\st => do (v, st') <- f st
                                 let ST kv = k v
                                 kv st')

implementation Monad m => MonadState stateType (StateT stateType m) where
    get   = ST (\x => pure (x, x))
    put x = ST (\y => pure ((), x))

implementation MonadTrans (StateT stateType) where
    lift x = ST (\st => do r <- x
                           pure (r, st))

||| Apply a function to modify the context of this computation
modify : MonadState stateType m => (stateType -> stateType) -> m ()
modify f = do s <- get
              put (f s)

||| Evaluate a function in the context held by this computation
gets : MonadState stateType m => (stateType -> a) -> m a
gets f = do s <- get
            pure (f s)

||| The State monad. See the MonadState interface
State : (stateType : Type) -> (ty : Type) -> Type
State = \s, a => StateT s Identity a

||| Unwrap a State monad computation.
runState : StateT stateType Identity a -> stateType -> (a, stateType)
runState act = runIdentity . runStateT act

||| Unwrap a State monad computation, but discard the final state.
evalState : State stateType a -> stateType -> a
evalState m = fst . runState m

||| Unwrap a State monad computation, but discard the resulting value.
execState : State stateType a -> stateType -> stateType
execState m = snd . runState m
