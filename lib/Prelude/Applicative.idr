module Prelude.Applicative

import Builtins
import Prelude.Functor

---- Applicative functors/Idioms

infixl 2 <$> 

class Functor f => Applicative (f : Type -> Type) where 
    pure  : a -> f a
    (<$>) : f (a -> b) -> f a -> f b

infixl 2 <$
(<$) : Applicative f => f a -> f b -> f a
a <$ b = fmap const a <$> b

infixl 2 $>
($>) : Applicative f => f a -> f b -> f b
a $> b = fmap (const id) a <$> b

infixl 3 <|>
class Applicative f => Alternative (f : Type -> Type) where
    empty : f a
    (<|>) : f a -> f a -> f a

guard : Alternative f => Bool -> f ()
guard a = if a then pure () else empty

when : Applicative f => Bool -> f () -> f ()
when a f = if a then f else pure ()

sequence : Applicative f => List (f a) -> f (List a)
sequence []        = pure []
sequence (x :: xs) = fmap (::) x <$> sequence xs

sequence_ : Applicative f => List (f a) -> f ()
sequence_ [] = pure ()
sequence_ (x :: xs) = x $> sequence_ xs

traverse : Applicative f => (a -> f b) -> List a -> f (List b)
traverse f xs = sequence (map f xs)

traverse_ : Applicative f => (a -> f b) -> List a -> f ()
traverse_ f (x :: xs) = f x $> traverse_ f xs
