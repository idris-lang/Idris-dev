module Prelude.Applicative

import Builtins
import Prelude.Basics
import Prelude.Classes
import Prelude.Functor

---- Applicative functors/Idioms

infixl 2 <$>

class Functor f => Apply (f : Type -> Type) where
	(<$>) : f (a -> b) -> f a -> f b

class Apply f => Applicative (f : Type -> Type) where
    pure  : a -> f a

instance Apply id where
    f <$> a = f a
instance Applicative id where
	pure a = a

infixl 2 <$
(<$) : Apply f => f a -> f b -> f a
a <$ b = map const a <$> b

infixl 2 $>
($>) : Apply f => f a -> f b -> f b
a $> b = map (const id) a <$> b

||| Lift a function to an applicative
liftA : Applicative f => (a -> b) -> f a -> f b
liftA f a = pure f <$> a

||| Lift a two-argument function to an applicative
liftA2 : Apply f => (a -> b -> c) -> f a -> f b -> f c
liftA2 f a b = (map f a) <$> b

||| Lift a three-argument function to an applicative
liftA3 : Apply f => (a -> b -> c -> d) -> f a -> f b -> f c -> f d
liftA3 f a b c = (map f a) <$> b <$> c

infixl 3 <|>
class Functor f => Alt (f : Type -> Type) where
	(<|>) : f a -> f a -> f a
class Alt f => Plus (f : Type -> Type) where
	empty : f a
class (Applicative f, Plus f) => Alternative (f : Type -> Type)

||| `guard a` is `pure ()` if `a` is `True` and `empty` if `a` is `False`
guard : Alternative f => Bool -> f ()
guard a = if a then pure () else empty

||| Conditionally execute an applicative expression
when : Applicative f => Bool -> Lazy (f ()) -> f ()
when True f = Force f
when False f = pure ()
