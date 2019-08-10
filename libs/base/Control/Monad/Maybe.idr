module Control.Monad.Maybe

import Control.Monad.Trans

%access public export

data MaybeT : (m : Type -> Type) -> (a : Type) -> Type where
    MkMaybeT : m (Maybe a) -> MaybeT m a

runMaybeT : MaybeT m a -> m (Maybe a)
runMaybeT (MkMaybeT v) = v


Functor m => Functor (MaybeT m) where
    map f (MkMaybeT v) = MkMaybeT $ map (map f) v

Applicative m => Applicative (MaybeT m) where
    pure x = MkMaybeT (pure $ pure x)
    (<*>) (MkMaybeT x) (MkMaybeT y) =
            MkMaybeT (pure apply <*> x <*> y)
        where
        apply : Maybe (a -> b) -> Maybe a -> Maybe b
        apply mf ma = map (\(f, a) => f a) $ both mf ma

Monad m => Monad (MaybeT m) where
    (>>=) (MkMaybeT x) f = MkMaybeT $ do
        v <- x
        case v of
            Nothing => pure Nothing
            Just y  => runMaybeT (f y)

    join (MkMaybeT x) = MkMaybeT $ do
        ma <- x
        case ma of
            Nothing => pure Nothing
            Just m => runMaybeT m

MonadTrans MaybeT where
    lift x = MkMaybeT $ map Just x
