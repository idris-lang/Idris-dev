module Control.Monad.Writer

import Builtins
import Control.Monad.Identity
import Control.Monad.Trans

%access public

||| A monad representing a computation that produces a stream of output
class (Monoid w, Monad m) => MonadWriter w (m : Type -> Type) where
    ||| tell w produces the output w
    tell   : w -> m ()
    ||| Execute an action and add it's output to the value of the computation
    listen : m a -> m (a, w)
    ||| Execute an action and apply the returned function to the output
    pass   : m (a, w -> w) -> m a

||| The transformer base of the Writer monad
record WriterT : Type -> (Type -> Type) -> Type -> Type where
    WR : {m : Type -> Type} ->
         (runWriterT : m (a, w)) -> WriterT w m a

instance Functor f => Functor (WriterT w f) where
    map f (WR g) = WR $ map (\w => (f . fst $ w, snd w)) g

instance (Monoid w, Applicative m) => Applicative (WriterT w m) where
    pure a            = WR $ pure (a, neutral)
    (WR f) <*> (WR v) = WR $ liftA2 merge f v where
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
    tell w        = WR $ return ((), w)
    listen (WR m) = WR $ do (a, w) <- m
                            return ((a, w), w)
    pass (WR m)   = WR $ do ((a, f), w) <- m
                            return (a, f w)

instance Monoid w => MonadTrans (WriterT w) where
    lift x = WR $ do r <- x
                     return (r, neutral)

||| Run an action in the Writer monad and transform the written output
listens : MonadWriter w m => (w -> b) -> m a -> m (a, b)
listens {m} f act = listens' f (listen act) where
  listens' : (w -> b) -> m (a, w) -> m (a, b)
  listens' f' ma = do (a, w) <- ma
                      return (a, f' w)

||| Run an action, apply a function to it's output, and return it's value
censor : MonadWriter w m => (w -> w) -> m a -> m a
censor f m = pass $ do a <- m
                       return (a, f)

||| The Writer monad itself. See the MonadWriter class
Writer : Type -> Type -> Type
Writer w a = WriterT w Identity a
