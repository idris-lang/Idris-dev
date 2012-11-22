module Prelude.Monad

-- Monads and Functors

import Builtins
import Prelude.List
import Prelude.Applicative

%access public

infixl 5 >>=
infixr 1 <=<
infixl 1 >=>

-- Monad: instances should satisfy the following laws:
--   Functor bind:
--                     bind pure        == id
--     forall f g .    bind (f <=< g)   == bind f . bind g
--   Associativity of <=<:
--     forall f g h .  f <=< (g <=< h)  == (f <=< g) <=< h
--   Neutral element for <=<:
--     forall f .      f <=< pure       == f
--     forall f .      pure <=< f       == f

class Applicative m => Monad (m : Set -> Set) where 
    (>>=)  : m a -> (a -> m b) -> m b

--TODO: Remove (>>=) in favor of bind
    %assert_total
    bind : (a -> m b) -> (m a -> m b)
    bind = flip (>>=)
--  bind f = flatten . fmap f
    
    %assert_total
    flatten : m (m a) -> m a
    flatten = bind id

(<=<) : Monad m => (b -> m c) -> (a -> m b) -> (a -> m c)
f <=< g = bind f . g
   
(>=>) : Monad m => (a -> m b) -> (b -> m c) -> (a -> m c)
f >=> g = bind g . f 
    
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
