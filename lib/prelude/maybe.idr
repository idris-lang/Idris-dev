module prelude.maybe

import builtins

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

--------------------------------------------------------------------------------
-- Class instances
--------------------------------------------------------------------------------

maybe_bind : Maybe a -> (a -> Maybe b) -> Maybe b
maybe_bind Nothing  k = Nothing
maybe_bind (Just x) k = k x
