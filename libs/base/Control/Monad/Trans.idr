module Control.Monad.Trans

%access public export

interface MonadTrans (t : (Type -> Type) -> Type -> Type) where
    lift : Monad m => m a -> t m a
