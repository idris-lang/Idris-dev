module Prelude.Applicative

import Builtins

import Prelude.Basics
import Prelude.Bool
import Prelude.Interfaces
import Prelude.Foldable
import Prelude.Functor

%access public export

---- Applicative functors/Idioms

infixl 2 <*>

interface Functor f => Applicative (f : Type -> Type) where
    pure  : a -> f a
    (<*>) : f (a -> b) -> f a -> f b

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
interface Applicative f => Alternative (f : Type -> Type) where
    empty : f a
    (<|>) : f a -> f a -> f a

||| `guard a` is `pure ()` if `a` is `True` and `empty` if `a` is `False`
guard : Alternative f => Bool -> f ()
guard a = if a then pure () else empty

||| Conditionally execute an applicative expression
when : Applicative f => Bool -> Lazy (f ()) -> f ()
when True f = Force f
when False f = pure ()

||| Fold using Alternative
|||
||| If you have a left-biased alternative operator `<|>`, then `choice`
||| performs left-biased choice from a list of alternatives, which means that
||| it evaluates to the left-most non-`empty` alternative.
|||
||| If the list is empty, or all values in it are `empty`, then it
||| evaluates to `empty`.
|||
||| Example:
|||
||| ```
||| -- given a parser expression like:
||| expr = literal <|> keyword <|> funcall
|||
||| -- choice lets you write this as:
||| expr = choice [literal, keyword, funcall]
||| ```
|||
||| Note: In Haskell, `choice` is called `asum`.
choice : (Foldable t, Alternative f) => t (f a) -> f a
choice x = foldr (<|>) empty x

||| A fused version of choice and map.
choiceMap : (Foldable t, Alternative f) => (a -> f b) -> t a -> f b
choiceMap f x = foldr (\elt, acc => f elt <|> acc) empty x
