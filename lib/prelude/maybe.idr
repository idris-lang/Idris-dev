module prelude.maybe

import builtins
import prelude.list
import prelude.monad

data Maybe a
  = Nothing
  | Just a

--------------------------------------------------------------------------------
-- Syntactic tests
--------------------------------------------------------------------------------

isNothing : Maybe a -> Bool
isNothing Nothing  = True
isNothing (Just j) = False

isJust : Maybe a -> Bool
isJust Nothing  = False
isJust (Just j) = True

--------------------------------------------------------------------------------
-- Conversions
--------------------------------------------------------------------------------

maybeToList : Maybe a -> List a
maybeToList Nothing  = []
maybeToList (Just j) = [j]

listToMaybe : List a -> Maybe a
listToMaybe []      = Nothing
listToMaybe (x::xs) = Just x

--------------------------------------------------------------------------------
-- Misc
--------------------------------------------------------------------------------

maybe : |(def : b) -> (a -> b) -> Maybe a -> b
maybe n j Nothing  = n
maybe n j (Just x) = j x

fromMaybe : |(def: a) -> Maybe a -> a
fromMaybe def Nothing  = def
fromMaybe def (Just j) = j

toMaybe : Bool -> a -> Maybe a
toMaybe True  j = Just j
toMaybe False j = Nothing

catMaybes : List (Maybe a) -> List a
catMaybes []      = []
catMaybes (x::xs) =
  case x of
    Nothing => catMaybes xs
    Just j  => j :: catMaybes xs

mapMaybe : (a -> Maybe b) -> List a -> List b
mapMaybe f []      = []
mapMaybe f (x::xs) =
  case f x of
    Nothing => mapMaybe f xs
    Just j  => j :: mapMaybe f xs

--------------------------------------------------------------------------------
-- Class instances
--------------------------------------------------------------------------------

maybe_bind : Maybe a -> (a -> Maybe b) -> Maybe b
maybe_bind Nothing  k = Nothing
maybe_bind (Just x) k = k x
