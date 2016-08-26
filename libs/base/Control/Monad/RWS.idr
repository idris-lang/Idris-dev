module Control.Monad.RWS

import Control.Monad.Identity
import Control.Monad.State
import Control.Monad.Writer
import Control.Monad.Reader

%access public export

||| A combination of the Reader, Writer, and State monads
interface (Monoid w, MonadReader r m, MonadWriter w m, MonadState s m) => MonadRWS r w s (m : Type -> Type) | m where {}

||| The transformer on which the RWS monad is based
record RWST (r : Type) (w : Type) (s : Type) (m : Type -> Type) (a : Type) where
  constructor MkRWST
  runRWST : r -> s -> m (a, s, w)
  
implementation Monad m => Functor (RWST r w s m) where
    map f (MkRWST m) = MkRWST $ \r,s => do  (a, s', w) <- m r s
                                            pure (f a, s', w)

implementation (Monoid w, Monad m) => Applicative (RWST r w s m) where
    pure a = MkRWST $ \_,s => pure (a, s, neutral)
    (MkRWST f) <*> (MkRWST v) = MkRWST $ \r,s => do (a, s', w)   <- v r s
                                                    (fn, ss, w') <- f r s
                                                    pure (fn a, ss, w <+> w')

implementation (Monoid w, Monad m) => Monad (RWST r w s m) where
    (MkRWST m) >>= k = MkRWST $ \r,s => do  (a, s', w) <- m r s
                                            let MkRWST ka = k a
                                            (b, ss, w') <- ka r s'
                                            pure (b, ss, w <+> w')

implementation (Monoid w, Monad m) => MonadReader r (RWST r w s m) where
    ask                = MkRWST $ \r,s => pure (r, s, neutral)
    local f (MkRWST m) = MkRWST $ \r,s => m (f r) s

implementation (Monoid w, Monad m) => MonadWriter w (RWST r w s m) where
    tell w            = MkRWST $ \_,s => pure ((), s, w)
    listen (MkRWST m) = MkRWST $ \r,s => do (a, s', w) <- m r s
                                            pure ((a, w), s', w)
    pass (MkRWST m)   = MkRWST $ \r,s => do ((a, f), s', w) <- m r s
                                            pure (a, s', f w)

implementation (Monoid w, Monad m) => MonadState s (RWST r w s m) where
    get   = MkRWST $ \_,s => pure (s,  s, neutral)
    put s = MkRWST $ \_,_ => pure ((), s, neutral)

implementation (Monoid w, Monad m) => MonadRWS r w s (RWST r w s m) where {}

||| The RWS monad. See the MonadRWS interface
RWS : Type -> Type -> Type -> Type -> Type
RWS r w s a = RWST r w s Identity a
