interface Monad m => ContainerMonad (m : Type -> Type) where
    Elem : a -> m a -> Type
    tagElem : (mx : m a) -> m (x : a ** Elem x mx)

interface Monad m => ContainerMonad2 a (m : Type -> Type) where
    Elem2 : a -> m a -> Type
    tagElem2 : (mx : m a) -> m (x : a ** Elem2 x mx)

