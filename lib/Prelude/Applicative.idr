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
a <$ b = map const a <$> b

infixl 2 $>
($>) : Applicative f => f a -> f b -> f b
a $> b = map (const id) a <$> b

infixl 3 <|>
class Applicative f => Alternative (f : Type -> Type) where
    empty : f a
    (<|>) : f a -> f a -> f a

guard : Alternative f => Bool -> f ()
guard a = if a then pure () else empty

when : Applicative f => Bool -> f () -> f ()
when a f = if a then f else pure ()
