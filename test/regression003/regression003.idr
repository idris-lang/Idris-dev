module Main

data Free : (f : Type -> Type) -> (a : Type) -> Type where
  Pure : a -> Free f a
  Bind : f (Free f a) -> Free f a

Functor f => Functor (Free f) where
  map f m = assert_total $ case m of
    Pure x => Pure (f x)
    Bind x => Bind (map (map f) x)

Functor f => Applicative (Free f) where
  pure = Pure

  m <*> x = assert_total $ case m of
    Pure f => map f x
    Bind f => Bind (map (<*> x) f)

Functor f => Monad (Free f) where
  m >>= f = assert_total $ case m of
    Pure x => f x
    Bind x => Bind (map (>>= f) x)

liftFree : Functor f => f a -> Free f a
liftFree = assert_total $ Bind . map Pure

foldFree : (Monad m, Functor f) => ({ a : Type } -> f a -> m a) -> Free f b -> m b
foldFree f m = assert_total $ case m of
  Pure x => pure x
  Bind x => f x >>= foldFree f

data FileSystemF next
  = ReadFile (String -> next)

FileSystem : Type -> Type
FileSystem = Free FileSystemF

Functor FileSystemF where
  map f (ReadFile nextFn) = ReadFile (f . nextFn)

readFileF : FileSystem String
readFileF = liftFree $ ReadFile id



interpret2 : FileSystemF a -> IO a
interpret2 (ReadFile nextFn) = do
  contents <- pure "ola"
  pure (nextFn contents)

main : IO ()
main =
  do
    c <- foldFree interpret2 readFileF
    putStrLn' c

