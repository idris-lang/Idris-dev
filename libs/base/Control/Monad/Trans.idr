module Control.Monad.Trans

class MonadTrans (t : (Type -> Type) -> Type -> Type) where
    lift : Monad m => m a -> t m a
