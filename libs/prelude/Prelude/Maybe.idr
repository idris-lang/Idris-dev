module Prelude.Maybe

import Builtins
import Prelude.Algebra
import Prelude.Basics
import Prelude.Bool
import Prelude.Cast
import Prelude.Interfaces
import Prelude.Foldable
import Prelude.Uninhabited

%access public export
%default total

||| An optional value. This can be used to represent the possibility of
||| failure, where a function may return a value, or not.
data Maybe : (a : Type) -> Type where
    ||| No value stored
    Nothing : Maybe a
    ||| A value of type `a` is stored
    Just : (x : a) -> Maybe a

-- Used hints for erasure analysis
%used Just x

--------------------------------------------------------------------------------
-- Syntactic tests
--------------------------------------------------------------------------------

isNothing : Maybe a -> Bool
isNothing Nothing  = True
isNothing (Just j) = False

isJust : Maybe a -> Bool
isJust Nothing  = False
isJust (Just j) = True

||| Proof that some `Maybe` is actually `Just`
data IsJust : Maybe a -> Type where
  ItIsJust : IsJust (Just x)

Uninhabited (IsJust Nothing) where
  uninhabited ItIsJust impossible

||| Decide whether a 'Maybe' is 'Just'
isItJust : (v : Maybe a) -> Dec (IsJust v)
isItJust (Just x) = Yes ItIsJust
isItJust Nothing = No absurd

--------------------------------------------------------------------------------
-- Misc
--------------------------------------------------------------------------------

maybe : Lazy b -> Lazy (a -> b) -> Maybe a -> b
maybe n j Nothing  = n
maybe n j (Just x) = j x

||| Convert a `Maybe a` value to an `a` value by providing a default `a` value
||| in the case that the `Maybe` value is `Nothing`.
fromMaybe : (Lazy a) -> Maybe a -> a
fromMaybe def Nothing  = def
fromMaybe def (Just j) = j

||| Returns `Just` the given value if the conditional is `True`
||| and `Nothing` if the conditional is `False`.
toMaybe : Bool -> Lazy a -> Maybe a
toMaybe True  j = Just j
toMaybe False j = Nothing

justInjective : {x : t} -> {y : t} -> (Just x = Just y) -> x = y
justInjective Refl = Refl

||| Convert a `Maybe a` value to an `a` value, using `neutral` in the case
||| that the `Maybe` value is `Nothing`.
lowerMaybe : Monoid a => Maybe a -> a
lowerMaybe Nothing = neutral
lowerMaybe (Just x) = x

||| Returns `Nothing` when applied to `neutral`, and `Just` the value otherwise.
raiseToMaybe : (Monoid a, Eq a) => a -> Maybe a
raiseToMaybe x = if x == neutral then Nothing else Just x

--------------------------------------------------------------------------------
-- Interface implementations
--------------------------------------------------------------------------------

maybe_bind : Maybe a -> (a -> Maybe b) -> Maybe b
maybe_bind Nothing  k = Nothing
maybe_bind (Just x) k = k x

(Eq a) => Eq (Maybe a) where
  Nothing  == Nothing  = True
  Nothing  == (Just _) = False
  (Just _) == Nothing  = False
  (Just a) == (Just b) = a == b

||| Prioritised choice. Just like the `Alternative` implementation, the
||| `Semigroup` for `Maybe a` keeps the first succeeding computation.
|||
||| **NB**: This is a different choice than in the Haskell libraries.
||| Use `collectJust` to get the Haskell behaviour.
Semigroup (Maybe a) where
  Nothing   <+> m = m
  (Just x)  <+> _ = Just x

||| Transform any semigroup into a monoid by using `Nothing` as the
||| designated neutral element and collecting the contents of the
||| `Just` constructors using a semigroup structure on `a`. This is
||| the behaviour in the Haskell libraries.
[collectJust] Semigroup a => Semigroup (Maybe a) where
  Nothing   <+> m       = m
  m         <+> Nothing = m
  (Just m1) <+> (Just m2) = Just (m1 <+> m2)

Monoid (Maybe a) where
  neutral = Nothing

(Monoid a, Eq a) => Cast a (Maybe a) where
  cast = raiseToMaybe

(Monoid a) => Cast (Maybe a) a where
  cast = lowerMaybe

Foldable Maybe where
  foldr _ z Nothing  = z
  foldr f z (Just x) = f x z
