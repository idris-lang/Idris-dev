module Control.IOExcept

import Prelude

-- An IO monad with exception handling

data IOExcept : Type -> Type -> Type where
     ioM : IO (Either err a) -> IOExcept err a

instance Functor (IOExcept e) where
     fmap f (ioM fn) = ioM (fmap (fmap f) fn)

instance Applicative (IOExcept e) where
     pure x = ioM (pure (pure x))
     (ioM f) <$> (ioM a) = ioM (do f' <- f; a' <- a
                                   return (f' <$> a'))

instance Monad (IOExcept e) where
     (ioM x) >>= k = ioM (do x' <- x;
                             case x' of
                                  Right a => let (ioM ka) = k a in
                                                 ka
                                  Left err => return (Left err))

ioe_lift : IO a -> IOExcept err a
ioe_lift op = ioM (do op' <- op
                      return (Right op'))

ioe_fail : err -> IOExcept err a
ioe_fail e = ioM (return (Left e))

ioe_run : IOExcept err a -> (err -> IO b) -> (a -> IO b) -> IO b
ioe_run (ioM act) err ok = do act' <- act
                              case act' of
                                   Left e => err e
                                   Right v => ok v

