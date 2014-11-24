 module Prelude.Either

import Builtins

import Prelude.Maybe
import Prelude.List

||| A sum type
%elim data Either a b =
  ||| One possibility of the sum, conventionally used to represent errors
  Left a |
  ||| The other possibility, conventionally used to represent success
  Right b

--------------------------------------------------------------------------------
-- Syntactic tests
--------------------------------------------------------------------------------

||| True if the argument is Left, False otherwise
isLeft : Either a b -> Bool
isLeft (Left l)  = True
isLeft (Right r) = False

||| True if the argument is Right, False otherwise
isRight : Either a b -> Bool
isRight (Left l)  = False
isRight (Right r) = True

--------------------------------------------------------------------------------
-- Misc.
--------------------------------------------------------------------------------

||| Perform a case analysis on a Boolean, providing clients with a `So` proof
choose : (b : Bool) -> Either (So b) (So (not b))
choose True  = Left Oh
choose False = Right Oh

||| Simply-typed eliminator for Either
||| @ f the action to take on Left
||| @ g the action to take on Right
||| @ e the sum to analyze
either : (f : Lazy (a -> c)) -> (g : Lazy (b -> c)) -> (e : Either a b) -> c
either l r (Left x)  = (Force l) x
either l r (Right x) = (Force r) x

||| Keep the payloads of all Left constructors in a list of Eithers
lefts : List (Either a b) -> List a
lefts []      = []
lefts (x::xs) =
  case x of
    Left  l => l :: lefts xs
    Right r => lefts xs

||| Keep the payloads of all Right constructors in a list of Eithers
rights : List (Either a b) -> List b
rights []      = []
rights (x::xs) =
  case x of
    Left  l => rights xs
    Right r => r :: rights xs

||| Split a list of Eithers into a list of the left elements and a list of the right elements
partitionEithers : List (Either a b) -> (List a, List b)
partitionEithers l = (lefts l, rights l)

||| Remove a "useless" Either by collapsing the case distinction
fromEither : Either a a -> a
fromEither (Left l)  = l
fromEither (Right r) = r

--------------------------------------------------------------------------------
-- Conversions
--------------------------------------------------------------------------------

||| Convert a Maybe to an Either by using a default value in case of Nothing
||| @ e the default value
maybeToEither : (def : Lazy e) -> Maybe a -> Either e a
maybeToEither def (Just j) = Right j
maybeToEither def Nothing  = Left  def


--------------------------------------------------------------------------------
-- Instances
--------------------------------------------------------------------------------

instance (Eq a, Eq b) => Eq (Either a b) where
  (==) (Left x)  (Left y)  = x == y
  (==) (Right x) (Right y) = x == y
  (==) _         _         = False



--------------------------------------------------------------------------------
-- Injectivity of constructors
--------------------------------------------------------------------------------

||| Left is injective
total leftInjective : {b : Type} -> {x : a} -> {y : a}
                    -> (Left {b = b} x = Left {b = b} y) -> (x = y)
leftInjective Refl = Refl

||| Right is injective
total rightInjective : {a : Type} -> {x : b} -> {y : b}
                     -> (Right {a = a} x = Right {a = a} y) -> (x = y)
rightInjective Refl = Refl
