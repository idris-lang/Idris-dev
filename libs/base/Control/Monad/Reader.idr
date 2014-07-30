module Control.Monad.Reader

import Builtins
import Control.Monad.Identity

%access public

class Monad m => MonadReader r (m : Type -> Type) where
    ask   : m r
    local : (r -> r) -> m a -> m a

record ReaderT : Type -> (Type -> Type) -> Type -> Type where
    RD : {m : Type -> Type} ->
         (runReaderT : r -> m a) -> ReaderT r m a

liftReaderT : {m : Type -> Type} -> m a -> ReaderT r m a
liftReaderT m = RD $ const m

instance Functor f => Functor (ReaderT r f) where
    map f (RD g) = RD $ (map f) . g

instance Apply m => Apply (ReaderT r m) where
    (RD f) <$> (RD v) = RD $ \r => f r <$> v r
instance Applicative m => Applicative (ReaderT r m) where
    pure              = liftReaderT . pure

instance Alt m => Alt (ReaderT r m) where
    (RD m) <|> (RD n) = RD $ \r => m r <|> n r
instance Plus m => Plus (ReaderT r m) where
    empty             = liftReaderT empty

instance Bind m => Bind (ReaderT r m) where
    (RD f) >>= k = RD $ \r => do a <- f r
                                 let RD ka = k a
                                 ka r
instance Monad m => Monad (ReaderT r m) where

instance Monad m => MonadReader r (ReaderT r m) where
    ask            = RD return
    local f (RD m) = RD $ m . f

asks : MonadReader r m => (r -> a) -> m a
asks f = do r <- ask
            return (f r)

Reader : Type -> Type -> Type
Reader r a = ReaderT r Identity a
