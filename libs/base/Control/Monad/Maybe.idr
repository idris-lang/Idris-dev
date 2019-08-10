module Control.Monad.Maybe

import Control.Monad.Trans

%access public export

record MaybeT (m : Type -> Type) (a : Type) where
  constructor MkMaybeT
  runMaybeT : m (Maybe a)


Functor m => Functor (MaybeT m) where
    map f (MkMaybeT v) = MkMaybeT $ map (map f) v

Applicative m => Applicative (MaybeT m) where
    pure x = MkMaybeT (pure $ pure x)
    (<*>) (MkMaybeT x) (MkMaybeT y) = MkMaybeT [| x <*> y |]

Monad m => Monad (MaybeT m) where
    (>>=) (MkMaybeT x) f = MkMaybeT $ x >>= maybe (pure Nothing) (runMaybeT . f)
    join (MkMaybeT x) = MkMaybeT $ x >>= maybe (pure Nothing) runMaybeT

MonadTrans MaybeT where
    lift x = MkMaybeT $ map Just x
