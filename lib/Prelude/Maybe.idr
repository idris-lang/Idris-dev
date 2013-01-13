module Prelude.Maybe

import Builtins
import Prelude.Algebra

%access public
%default total

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

-- | Lift a semigroup into 'Maybe' forming a 'Monoid' according to
-- <http://en.wikipedia.org/wiki/Monoid>: \"Any semigroup S may be
-- turned into a monoid simply by adjoining an element e not in S
-- and defining i+i = i and i+s = s = s+i for all s ∈ S.\"

instance (Semigroup a) => Semigroup (Maybe a) where
  Nothing <+> m = m
  m <+> Nothing = m
  (Just m1) <+> (Just m2) = Just (m1 <+> m2)

instance (Monoid a) => Monoid (Maybe a) where
  neutral = Nothing
