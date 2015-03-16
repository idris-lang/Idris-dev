module Control.Monad.Reader

import Builtins
import Control.Monad.Identity
import Control.Monad.Trans

%access public

||| A monad representing a computation that runs in an immutable context
class Monad m => MonadReader r (m : Type -> Type) where
    ||| Return the context
    ask   : m r
    ||| Temprorarily modify the input and run an action in the new context
    local : (r -> r) -> m a -> m a

||| The transformer on which the Reader monad is based
record ReaderT (r : Type) (m : Type -> Type) (a : Type) where
  runReaderT : r -> m a
  constructor RD

{-
record ReaderT : Type -> (Type -> Type) -> Type -> Type where
    RD : {m : Type -> Type} ->
         (runReaderT : r -> m a) -> ReaderT r m a
-}
||| Create a ReaderT with an empty context
liftReaderT : {m : Type -> Type} -> m a -> ReaderT r m a
liftReaderT m = RD $ const m

instance Functor f => Functor (ReaderT r f) where
    map f (RD g) = RD $ (map f) . g

instance Applicative m => Applicative (ReaderT r m) where
    pure              = liftReaderT . pure
    (RD f) <*> (RD v) = RD $ \r => f r <*> v r

instance Alternative m => Alternative (ReaderT r m) where
    empty             = liftReaderT empty
    (RD m) <|> (RD n) = RD $ \r => m r <|> n r

instance Monad m => Monad (ReaderT r m) where
    (RD f) >>= k = RD $ \r => do a <- f r
                                 let RD ka = k a
                                 ka r

instance Monad m => MonadReader r (ReaderT r m) where
    ask            = RD return
    local f (RD m) = RD $ m . f

instance MonadTrans (ReaderT r) where
    lift x = RD (const x)

||| Evaluate a function in the context of a Reader monad
asks : MonadReader r m => (r -> a) -> m a
asks f = do r <- ask
            return (f r)

||| The reader monad. See MonadReader
Reader : Type -> Type -> Type
Reader r a = ReaderT r Identity a
