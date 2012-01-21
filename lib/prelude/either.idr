module prelude.either

import builtins

import prelude.maybe
import prelude.list

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

either : Either a b -> (a -> c) -> (b -> c) -> c
either (Left x)  l r = l x
either (Right x) l r = r x

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
