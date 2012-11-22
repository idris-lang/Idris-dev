module Control.Functor.Identity

import Prelude.Functor
import Prelude.Applicative
import Prelude.Monad 

public record Identity : Set -> Set where
    Id : (runIdentity : a) -> Identity a

instance Functor Identity where
    fmap fn (Id a) = Id (fn a)

instance Applicative Identity where
    pure x = Id x
    
    (Id f) <$> (Id g) = Id (f g)

instance Monad Identity where
    (Id x) >>= k = k x
