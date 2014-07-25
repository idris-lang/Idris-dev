module Control.Monad.Identity

public record Identity : Type -> Type where
    Id : (runIdentity : a) -> Identity a

instance Functor Identity where
    map fn (Id a) = Id (fn a)

instance Apply Identity where
    (Id f) <$> (Id g) = Id (f g)
instance Applicative Identity where
    pure x = Id x

instance Bind Identity where
    (Id x) >>= k = k x
instance Monad Identity where
