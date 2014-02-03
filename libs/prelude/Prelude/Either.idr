module Prelude.Either

import Builtins

import Prelude.Maybe
import Prelude.List

data Either a b
  = Left a
  | Right b

--------------------------------------------------------------------------------
-- Syntactic tests
--------------------------------------------------------------------------------

isLeft : Either a b -> Bool
isLeft (Left l)  = True
isLeft (Right r) = False

isRight : Either a b -> Bool
isRight (Left l)  = False
isRight (Right r) = True

--------------------------------------------------------------------------------
-- Misc.
--------------------------------------------------------------------------------

choose : (b : Bool) -> Either (so b) (so (not b))
choose True  = Left oh
choose False = Right oh

either : (a -> c) -> (b -> c) -> Either a b -> c
either l r (Left x)  = l x
either l r (Right x) = r x

lefts : List (Either a b) -> List a
lefts []      = []
lefts (x::xs) =
  case x of
    Left  l => l :: lefts xs
    Right r => lefts xs

rights : List (Either a b) -> List b
rights []      = []
rights (x::xs) =
  case x of
    Left  l => rights xs
    Right r => r :: rights xs

partitionEithers : List (Either a b) -> (List a, List b)
partitionEithers l = (lefts l, rights l)

fromEither : Either a a -> a
fromEither (Left l)  = l
fromEither (Right r) = r

--------------------------------------------------------------------------------
-- Conversions
--------------------------------------------------------------------------------

maybeToEither : e -> Maybe a -> Either e a
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

total leftInjective : {b : Type} -> {x : a} -> {y : a}
                    -> (Left {b = b} x = Left {b = b} y) -> (x = y)
leftInjective refl = refl

total rightInjective : {a : Type} -> {x : b} -> {y : b}
                     -> (Right {a = a} x = Right {a = a} y) -> (x = y)
rightInjective refl = refl
