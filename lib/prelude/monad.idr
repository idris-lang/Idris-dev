module prelude.monad

-- Monads and Functors

import builtins
import prelude.list

%access public

infixl 5 >>=

class Monad (m : Set -> Set) where 
    return : a -> m a
    (>>=)  : m a -> (a -> m b) -> m b

class Functor (f : Set -> Set) where 
    fmap : (a -> b) -> f a -> f b

class Monad m => MonadPlus (m : Set -> Set) where 
    mplus : m a -> m a -> m a
    mzero : m a

guard : MonadPlus m => Bool -> m ()
guard True  = return ()
guard False = mzero

when : Monad m => Bool -> m () -> m ()
when True  f = f
when False _ = return ()

sequence : Monad m => List (m a) -> m (List a)
sequence []        = return []
sequence (x :: xs) = [ x' :: xs' | x' <- x, xs' <- sequence xs ]

sequence_ : Monad m => List (m a) -> m ()
sequence_ [] = return ()
sequence_ (x :: xs) = do x; sequence_ xs

mapM : Monad m => (a -> m b) -> List a -> m (List b)
mapM f xs = sequence (map f xs)

mapM_ : Monad m => (a -> m b) -> List a -> m ()
mapM_ f xs = sequence_ (map f xs)


