module Control.Monad.Trans

interface MonadTrans (t : (Type -> Type) -> Type -> Type) where
    lift : Monad m => m a -> t m a
