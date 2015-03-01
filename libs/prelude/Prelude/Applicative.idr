module Prelude.Applicative

import Builtins

import Prelude.Basics
import Prelude.Bool
import Prelude.Classes
import Prelude.Functor

---- Applicative functors/Idioms

infixl 2 <*>

class Functor f => Applicative (f : Type -> Type) where
    pure  : a -> f a
    (<*>) : f (a -> b) -> f a -> f b

instance Applicative id where
    pure a = a
    f <*> a = f a

class (Applicative f, VerifiedFunctor f) => VerifiedApplicative (f : Type -> Type) where
  applicativeMap : (x : f a) -> (g : a -> b) ->
                   map g x = pure g <*> x
  applicativeIdentity : (x : f a) -> pure id <*> x = x
  applicativeComposition : (x : f a) -> (g1 : f (a -> b)) -> (g2 : f (b -> c)) ->
                           ((pure (.) <*> g2) <*> g1) <*> x = g2 <*> (g1 <*> x)
  applicativeHomomorphism : (x : a) -> (g : a -> b) ->
                            (<*>) {f} (pure g) (pure x) = pure {f} (g x)
  applicativeInterchange : (x : a) -> (g : f (a -> b)) ->
                           g <*> pure x = pure (\g' : a -> b => g' x) <*> g

infixl 2 <*
(<*) : Applicative f => f a -> f b -> f a
a <* b = map const a <*> b

infixl 2 *>
(*>) : Applicative f => f a -> f b -> f b
a *> b = map (const id) a <*> b

||| Lift a function to an applicative
liftA : Applicative f => (a -> b) -> f a -> f b
liftA f a = pure f <*> a

||| Lift a two-argument function to an applicative
liftA2 : Applicative f => (a -> b -> c) -> f a -> f b -> f c
liftA2 f a b = (map f a) <*> b

||| Lift a three-argument function to an applicative
liftA3 : Applicative f => (a -> b -> c -> d) -> f a -> f b -> f c -> f d
liftA3 f a b c = (map f a) <*> b <*> c

infixl 3 <|>
class Applicative f => Alternative (f : Type -> Type) where
    empty : f a
    (<|>) : f a -> f a -> f a

||| `guard a` is `pure ()` if `a` is `True` and `empty` if `a` is `False`
guard : Alternative f => Bool -> f ()
guard a = if a then pure () else empty

||| Conditionally execute an applicative expression
when : Applicative f => Bool -> Lazy (f ()) -> f ()
when True f = Force f
when False f = pure ()
