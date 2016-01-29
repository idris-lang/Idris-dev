module Control.IOExcept

%access public export

-- An IO monad with exception handling

record IOExcept' (f:FFI) err a where
     constructor IOM
     runIOExcept : IO' f (Either err a)

Functor (IOExcept' f e) where
     map f (IOM fn) = IOM (map (map f) fn)

Applicative (IOExcept' f e) where
     pure x = IOM (pure (pure x))
     (IOM f) <*> (IOM a) = IOM [| f <*> a |]

Monad (IOExcept' f e) where
     (IOM x) >>= f = IOM $ x >>= either (pure . Left) (runIOExcept . f)

ioe_lift : IO' f a -> IOExcept' f err a
ioe_lift op = IOM $ map Right op

ioe_fail : err -> IOExcept' f err a
ioe_fail e = IOM $ pure (Left e)

ioe_run : IOExcept' f err a -> (err -> IO' f b) -> (a -> IO' f b) -> IO' f b
ioe_run (IOM act) err ok = either err ok !act

IOExcept : Type -> Type -> Type
IOExcept = IOExcept' FFI_C
