module Control.IOExcept

-- An IO monad with exception handling

record IOExcept err a where
     constructor IOM
     runIOExcept : IO (Either err a)

implementation Functor (IOExcept e) where
     map f (IOM fn) = IOM (map (map f) fn)

implementation Applicative (IOExcept e) where
     pure x = IOM (pure (pure x))
     (IOM f) <*> (IOM a) = IOM [| f <*> a |]

implementation Monad (IOExcept e) where
     (IOM x) >>= f = IOM $ x >>= either (pure . Left) (runIOExcept . f)

ioe_lift : IO a -> IOExcept err a
ioe_lift op = IOM $ map Right op

ioe_fail : err -> IOExcept err a
ioe_fail e = IOM $ pure (Left e)

ioe_run : IOExcept err a -> (err -> IO b) -> (a -> IO b) -> IO b
ioe_run (IOM act) err ok = either err ok !act
