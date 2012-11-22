module Control.Comonad

-- Monads and Functors

import Builtins
import Prelude.List
import Prelude.Applicative

%access public

infixl 5 =>>
infixr 1 =<=
infixl 1 =>=

-- Comonad: instances should satisfy the following laws:
--   Functor extend:
--                     extend extract   == id
--     forall f g .    extend (f =<= g) == extend f . extend g
--   Associativity of =<=:
--     forall f g h .  f =<= (g =<= h)  == (f =<= g) =<= h
--   Neutral element for =<=:
--     forall f .      f =<= extract    == f
--     forall f .      extract =<= f    == f

class Functor w => Comonad (w : Set -> Set) where
--TODO: Decide if we want to seperate extend from extract
--      to get a Semigroupoid instance for (=<=).
    extract : w a -> a

    extend  : (w a -> b) -> (w a -> w b)
    extend f = fmap f . duplicate
    
    duplicate : w a -> w (w a)
    duplicate = extend id

(=<=) : Comonad w => (w b -> c) -> (w a -> b) -> (w a -> c)
f =<= g = f . extend g
    
(=>=) : Comonad w => (w a -> b) -> (w b -> c) -> (w a -> c)
f =>= g = g . extend f
    