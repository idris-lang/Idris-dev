module Control.Monad.Reader

import Builtins
import Control.Monad.Identity
import Prelude.Monad
import Prelude.Applicative
import Prelude.Functor

%access public

class Monad m => MonadReader r (m : Type -> Type) where
    ask   : m r
    local : (r -> r) -> m a -> m a
    asks  : (r -> a) -> m a

record ReaderT : Type -> (Type -> Type) -> Type -> Type where
    RD : {m : Type -> Type} ->
         (runReaderT : r -> m a) -> ReaderT r m a

liftReaderT : {m : Type -> Type} -> m a -> ReaderT r m a
liftReaderT m = RD $ const m

instance Functor f => Functor (ReaderT r f) where
    map f (RD g) = RD $ (map f) . g

instance Applicative m => Applicative (ReaderT r m) where
    pure              = liftReaderT . pure
    (RD f) <$> (RD v) = RD $ \r => f r <$> v r

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
    asks f         = RD $ return . f

Reader : Type -> Type -> Type
Reader r a = ReaderT r Identity a
