module Control.Monad.Writer

import Builtins
import Control.Monad.Identity
import Prelude.Monad
import Prelude.Applicative
import Prelude.Functor

%access public

class (Monoid w, Monad m) => MonadWriter w (m : Type -> Type) where
    tell    : w -> m ()
    listen  : m a -> m (a, w)
    listens : (w -> b) -> m a -> m (a, b)
    pass    : m (a, w -> w) -> m a
    censor  : (w -> w) -> m a -> m a

record WriterT : Type -> (Type -> Type) -> Type -> Type where
    WR : {m : Type -> Type} ->
         (runWriterT : m (a, w)) -> WriterT w m a

instance Functor f => Functor (WriterT w f) where
    map f (WR g) = WR $ map (\w => (f . fst $ w, snd w)) g

instance (Monoid w, Applicative m) => Applicative (WriterT w m) where
    pure a            = WR $ pure (a, neutral)
    (WR f) <$> (WR v) = WR $ liftA2 merge f v where
        merge (fn, w) (a, w') = (fn a, w <+> w')

instance (Monoid w, Alternative m) => Alternative (WriterT w m) where
    empty             = WR empty
    (WR m) <|> (WR n) = WR $ m <|> n

instance (Monoid w, Monad m) => Monad (WriterT w m) where
    (WR m) >>= k = WR $ do (a, w) <- m
                           let WR ka = k a
                           (b, w') <- ka
                           return (b, w <+> w')

instance (Monoid w, Monad m) => MonadWriter w (WriterT w m) where
    tell w           = WR $ return ((), w)
    listen (WR m)    = WR $ do (a, w) <- m
                               return ((a, w), w)
    listens f (WR m) = WR $ do (a, w) <- m
                               return ((a, f w), w)
    pass (WR m)      = WR $ do ((a, f), w) <- m
                               return (a, f w)
    censor f (WR m)  = WR $ do (a, w) <- m
                               return (a, f w)


Writer : Type -> Type -> Type
Writer w a = WriterT w Identity a
