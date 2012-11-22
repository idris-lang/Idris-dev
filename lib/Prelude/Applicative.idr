module Prelude.Applicative

import Builtins
import Prelude.Functor

---- Applicative functors/Idioms

infixl 2 <$> 

-- ap :: Applicative f => f (a -> b) -> (f a -> f b)
-- ap = (<$>)
--
-- (<~<) :: Applicative f => f (b -> c) -> f (a -> b) -> f (a -> c)
-- f <~< g = ap (fmap (.) f) g 
--
-- Applicative: instances should satisfy the following laws:
--   Functor pure:
--                     pure id          == id
--     forall f g .    pure (f . g)     == pure f <~< pure g
--   Functor ap:
--                     ap (pure id)     == id
--     forall f g .    ap (f <~< g)     == ap f . ap g
--   Associativity of <~<:
--     forall f g h .  f <~< (g <~< h)  == (f <~< g) <~< h
--   Neutral element for <~<:
--     forall f .      f <~< pure id    == f
--     forall f .      pure id <~< f    == f

--TODO: check if these laws are precisely the required laws.

class Functor f => Applicative (f : Set -> Set) where 
    pure  : a -> f a
    (<$>) : f (a -> b) -> f a -> f b 

    (>>) : f a -> f b -> f b
    a >> b = pure (const id) <$> a <$> b 

