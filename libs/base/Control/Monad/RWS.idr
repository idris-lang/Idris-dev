module Control.Monad.RWS

import Builtins
import Control.Monad.Identity
import Control.Monad.State
import Control.Monad.Writer
import Control.Monad.Reader
import Prelude.Monad
import Prelude.Functor

%access public

class (Monoid w, MonadReader r m, MonadWriter w m, MonadState s m) => MonadRWS r w s (m : Type -> Type) where {}

record RWST : Type -> Type -> Type -> (Type -> Type) -> Type -> Type where
    MkRWST : {m : Type -> Type} ->
             (runRWST : r -> s -> m (a, s, w)) -> RWST r w s m a

instance Monad m => Functor (RWST r w s m) where
    map f (MkRWST m) = MkRWST $ \r => \s => do (a, s', w) <- m r s
                                               return (f a, s', w)

instance (Monoid w, Monad m) => Applicative (RWST r w s m) where
    pure a = MkRWST $ \_ => \s => return (a, s, neutral)
    (MkRWST f) <$> (MkRWST v) = MkRWST $ \r => \s => do (a, s', w)   <- v r s
                                                        (fn, ss, w') <- f r s
                                                        return (fn a, ss, w <+> w)

instance (Monoid w, Monad m) => Monad (RWST r w s m) where
    (MkRWST m) >>= k = MkRWST $ \r => \s => do (a, s', w) <- m r s
                                               let MkRWST ka = k a
                                               (b, ss, w') <- ka r s'
                                               return (b, ss, w <+> w')

instance (Monoid w, Monad m) => MonadReader r (RWST r w s m) where
    ask                = MkRWST $ \r => \s => return (r, s, neutral)
    local f (MkRWST m) = MkRWST $ \r => \s => m (f r) s

instance (Monoid w, Monad m) => MonadWriter w (RWST r w s m) where
    tell w            = MkRWST $ \_ => \s => return ((), s, w)
    listen (MkRWST m) = MkRWST $ \r => \s => do (a, s', w) <- m r s
                                                return ((a, w), s', w)
    pass (MkRWST m)   = MkRWST $ \r => \s => do ((a, f), s', w) <- m r s
                                                return (a, s', f w)

instance (Monoid w, Monad m) => MonadState s (RWST r w s m) where
    get   = MkRWST $ \_ => \s => return (s,  s, neutral)
    put s = MkRWST $ \_ => \_ => return ((), s, neutral)

instance (Monoid w, Monad m) => MonadRWS r w s (RWST r w s m) where {}

RWS : Type -> Type -> Type -> Type -> Type
RWS r w s a = RWST r w s Identity a
