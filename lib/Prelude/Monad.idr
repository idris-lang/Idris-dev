module Prelude.Monad

-- Monads and Functors

import Builtins
import Prelude.List
import Prelude.Applicative

%access public

infixl 5 >>=

class Applicative m => Monad (m : Set -> Set) where 
    (>>=)  : m a -> (a -> m b) -> m b

    %assert_total
    bind : (a -> m b) -> (m a -> m b)
    bind = flip (>>=)
    
    %assert_total
    flatten : m (m a) -> m a
    flatten = bind id
    
class Monad m => MonadPlus (m : Set -> Set) where 
    mplus : m a -> m a -> m a
    mzero : m a

guard : MonadPlus m => Bool -> m ()
guard True  = pure ()
guard False = mzero

when : Monad m => Bool -> m () -> m ()
when True  f = f
when False _ = pure ()

sequence : Monad m => List (m a) -> m (List a)
sequence []        = pure []
sequence (x :: xs) = [ x' :: xs' | x' <- x, xs' <- sequence xs ]

sequence_ : Monad m => List (m a) -> m ()
sequence_ [] = pure ()
sequence_ (x :: xs) = do x; sequence_ xs

mapM : Monad m => (a -> m b) -> List a -> m (List b)
mapM f xs = sequence (map f xs)

mapM_ : Monad m => (a -> m b) -> List a -> m ()
mapM_ f xs = sequence_ (map f xs)
