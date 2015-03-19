module Control.Monad.Identity

public record Identity (a : Type) where
  constructor Id
  runIdentity : a

instance Functor Identity where
    map fn (Id a) = Id (fn a)

instance Applicative Identity where
    pure x = Id x

    (Id f) <*> (Id g) = Id (f g)

instance Monad Identity where
    (Id x) >>= k = k x
