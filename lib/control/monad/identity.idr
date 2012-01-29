module control.monad.identity

import prelude.monad 

public record Identity : Set -> Set where
    Id : (runIdentity : a) -> Identity a

instance Monad Identity where
    return x = Id x
    (Id x) >>= k = k x
