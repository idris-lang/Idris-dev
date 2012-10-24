module Control.Monad.Identity

import Prelude.Monad 

public record Identity : Set -> Set where
    Id : (runIdentity : a) -> Identity a

instance Monad Identity where
    return x = Id x
    (Id x) >>= k = k x
