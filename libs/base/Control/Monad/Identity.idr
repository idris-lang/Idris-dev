module Control.Monad.Identity

%access public export

public export record Identity (a : Type) where
  constructor Id
  runIdentity : a

implementation Functor Identity where
    map fn (Id a) = Id (fn a)

implementation Applicative Identity where
    pure x = Id x

    (Id f) <*> (Id g) = Id (f g)

implementation Monad Identity where
    (Id x) >>= k = k x
