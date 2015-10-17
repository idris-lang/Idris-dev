module Control.IOExcept

-- An IO monad with exception handling

data IOExcept : Type -> Type -> Type where
     IOM : IO (Either err a) -> IOExcept err a

instance Functor (IOExcept e) where
     map f (IOM fn) = IOM (map (map f) fn)

instance Applicative (IOExcept e) where
     pure x = IOM (pure (pure x))
     (IOM f) <*> (IOM a) = IOM (do f' <- f; a' <- a
                                   return (f' <*> a'))

instance Monad (IOExcept e) where
     (IOM x) >>= k = IOM (do x' <- x;
                             case x' of
                                  Right a => let (IOM ka) = k a in
                                                 ka
                                  Left err => return (Left err))

ioe_lift : IO a -> IOExcept err a
ioe_lift op = IOM (do op' <- op
                      return (Right op'))

ioe_fail : err -> IOExcept err a
ioe_fail e = IOM (return (Left e))

ioe_run : IOExcept err a -> (err -> IO b) -> (a -> IO b) -> IO b
ioe_run (IOM act) err ok = do act' <- act
                              case act' of
                                   Left e => err e
                                   Right v => ok v

