module Control.Monad.Reader

import Builtins
import Control.Monad.Identity
import Control.Monad.Trans

%access public export

||| A monad representing a computation that runs in an immutable context
interface Monad m => MonadReader r (m : Type -> Type) | m where
    ||| Return the context
    ask   : m r
    ||| Temprorarily modify the input and run an action in the new context
    local : (r -> r) -> m a -> m a

||| The transformer on which the Reader monad is based
record ReaderT (r : Type) (m : Type -> Type) (a : Type) where
  constructor RD
  runReaderT : r -> m a

||| Create a ReaderT with an empty context
liftReaderT : {m : Type -> Type} -> m a -> ReaderT r m a
liftReaderT m = RD $ const m

implementation Functor f => Functor (ReaderT r f) where
    map f (RD g) = RD $ (map f) . g

implementation Applicative m => Applicative (ReaderT r m) where
    pure              = liftReaderT . pure
    (RD f) <*> (RD v) = RD $ \r => f r <*> v r

implementation Alternative m => Alternative (ReaderT r m) where
    empty             = liftReaderT empty
    (RD m) <|> (RD n) = RD $ \r => m r <|> n r

implementation Monad m => Monad (ReaderT r m) where
    (RD f) >>= k = RD $ \r => do a <- f r
                                 let RD ka = k a
                                 ka r

implementation Monad m => MonadReader r (ReaderT r m) where
    ask            = RD pure
    local f (RD m) = RD $ m . f

implementation MonadTrans (ReaderT r) where
    lift x = RD (const x)

||| Evaluate a function in the context of a Reader monad
asks : MonadReader r m => (r -> a) -> m a
asks f = do r <- ask
            pure (f r)

||| The reader monad. See MonadReader
Reader : Type -> Type -> Type
Reader r a = ReaderT r Identity a
